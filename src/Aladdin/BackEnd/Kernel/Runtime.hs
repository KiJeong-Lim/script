module Aladdin.BackEnd.Kernel.Runtime where

import Aladdin.BackEnd.Back
import Aladdin.BackEnd.Kernel.HOPU
import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.State.Strict
import Data.Functor.Identity
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Unique
import Lib.Base

type Fact = TermNode

type Facts = [Fact]

type Goal = TermNode

type Dummy = [DummyItem]

type Stack = [Dummy]

type Satisfied = String

type MoreAnswer = Bool

data Context
    = Context
        { _Scope :: ScopeLevel
        , _Subst :: VarBinding
        , _Label :: Labeling
        , _Lefts :: [Disagreement]
        }
    deriving ()

data DummyItem
    = Proves Context Goal
    | Discharge Unique
    deriving ()

data RTErr
    = RTErr
        { _ErrorCause :: String
        , _CurrentEnv :: (Dummy, Stack)
        }
    deriving ()

data Controller
    = Controller
        { _GetStr :: IO (Maybe String)
        , _PutStr :: String -> IO ()
        , _Answer :: Context -> IO MoreAnswer
        }
    deriving ()

instance Show RTErr where
    show = flip (showsPrec 0) ""
    showList = strcat . map (showsPrec 0)
    showsPrec _ (RTErr { _ErrorCause = error_cause, _CurrentEnv = (item, stack) }) = strcat
        [ strstr error_cause . nl
        , showsCurrentState item stack . nl
        ]

showDummy :: Indentation -> Dummy -> String -> String
showDummy space = strcat . map go where
    go :: DummyItem -> String -> String
    go (Proves ctx goal) = strcat
        [ pindent space . strstr "- goal = " . showsPrec 0 goal . nl
        , pindent space . strstr "- context = Context" . nl
        , pindent (space + 4) . strstr "{ " . strstr "_Scope = " . showsPrec 0 (_Scope ctx) . nl
        , pindent (space + 4) . strstr ", " . strstr "_Subst = " . plist (space + 8) [ showsPrec 0 (LVar v) . strstr " +-> " . showsPrec 0 t | (v, t) <- Map.toList (getVarBinding (_Subst ctx)) ] . nl
        , pindent (space + 4) . strstr ", " . strstr "_Lefts = " . plist (space + 8) [ showsPrec 0 lhs . strstr " =?= " . showsPrec 0 rhs | Disagreement lhs rhs <- _Lefts ctx ] . nl
        , pindent (space + 4) . strstr "} " . nl
        ]
    go (Discharge uni) = pindent space . strstr "- discharge " . showsPrec 0 (hashUnique uni) . nl

showsCurrentState :: Dummy -> Stack -> String -> String
showsCurrentState dummy1 stack2 = strcat
    [ strstr "* The top of the stack is:" . nl
    , showDummy 4 dummy1 . nl
    , strstr "* The rest of the stack is:" . nl
    , strcat
        [ strcat 
            [ pindent 2 . strstr "- [# " . showsPrec 0 i . strstr "]:" . nl
            , showDummy 4 dummy2 . nl
            ]
        | (i, dummy2) <- zip [1, 2 .. length stack2] stack2
        ]
    , strstr "--------------------------------" . nl
    ]

runtime :: Controller -> Facts -> Goal -> IO Satisfied
runtime (Controller get_str put_str answer) program = go where
    raise :: (MonadTrans t, Monad m) => e -> t (ExceptT e m) a
    raise = lift . throwE
    transit :: Dummy -> StateT (Map.Map Unique Fact, Stack) (ExceptT RTErr IO) (Maybe Context, Dummy)
    transit [] = do
        (hypotheses, stack) <- get
        case stack of
            [] -> return (Nothing, [])
            dummy : stack' -> do
                put (hypotheses, stack')
                transit dummy
    transit (Proves ctx goal : dummy) = do
        (hypotheses, stack) <- get
        let zonk = rewrite HNF . flatten (_Subst ctx)
            facts = program ++ Map.elems hypotheses
            defaultRTErr = RTErr
                { _ErrorCause = "An unknown error occured."
                , _CurrentEnv = ((Proves ctx goal : dummy), stack)
                }
        liftIO (put_str (showsCurrentState (Proves ctx goal : dummy) stack ""))
        liftIO get_str
        case unfoldlNApp (zonk goal) of
            (NCon (Atom { _ID = CI_Lambda }), args) -> raise (defaultRTErr { _ErrorCause = "`CI_Lambda\' cannot be head of goal." })
            (NCon (Atom { _ID = CI_If }), args) -> raise (defaultRTErr { _ErrorCause = "`CI_If\' cannot be head of goal." })
            (NCon (Atom { _ID = CI_True }), args)
                | [] <- args -> return (Just ctx, dummy)
                | otherwise -> raise (defaultRTErr { _ErrorCause = "The number of arguments of `CI_True\' must be 0." })
            (NCon (Atom { _ID = CI_Cut }), args)
                | [] <- args -> do
                    sequence
                        [ do
                            (hypotheses, stack) <- get
                            put (Map.delete uni hypotheses, stack)
                        | Discharge uni <- dummy
                        ]
                    return (Just ctx, [])
                | otherwise -> raise (defaultRTErr { _ErrorCause = "The number of arguments of `CI_Cut\' must be 0." })
            (NCon (Atom { _ID = CI_Fail }), args)
                | [] <- args -> transit dummy
                | otherwise -> raise (defaultRTErr { _ErrorCause = "The number of arguments of `CI_Fail\' must be 0." })
            (NCon (Atom { _ID = CI_And }), args)
                | [goal1, goal2] <- args -> do
                    output <- transit (Proves ctx goal1 : dummy)
                    case output of
                        (Nothing, dummy') -> transit dummy'
                        (Just ctx', dummy') -> transit (Proves ctx' goal2 : dummy')
                | otherwise -> raise (defaultRTErr { _ErrorCause = "The number of arguments of `CI_And\' must be 2." })
            (NCon (Atom { _ID = CI_Or }), args)
                | [goal1, goal2] <- args -> transit (Proves ctx goal1 : Proves ctx goal2 : dummy)
                | otherwise -> raise (defaultRTErr { _ErrorCause = "The number of arguments of `CI_Or\' must be 2." })
            (NCon (Atom { _ID = CI_Imply }), args)
                | [fact1, goal2] <- args -> do
                    uni <- liftIO newUnique
                    put (Map.insert uni fact1 hypotheses, stack)
                    transit (Proves ctx goal2 : Discharge uni : dummy)
                | otherwise -> raise (defaultRTErr { _ErrorCause = "The number of arguments of `CI_Imply\' must be 2." })
            (NCon (Atom { _ID = CI_Sigma }), args)
                | [goal1] <- args -> do
                    uni <- liftIO newUnique
                    let v = mkTermAtom (VI_Unique uni)
                        ctx' = ctx { _Label = enterID v (_Scope ctx) (_Label ctx) }
                    transit (Proves ctx' (mkNApp goal1 (mkLVar v)) : dummy)
                | otherwise -> raise (defaultRTErr { _ErrorCause = "The number of arguments of `CI_Sigma\' must be 1." })
            (NCon (Atom { _ID = CI_Pi }), args)
                | [goal1] <- args -> do
                    uni <- liftIO newUnique
                    let c = mkTermAtom (CI_Unique uni)
                        ctx' = ctx { _Label = enterID c (_Scope ctx + 1) (_Label ctx), _Scope = _Scope ctx + 1 }
                    transit (Proves ctx' (mkNApp goal1 (mkNCon c)) : dummy)
                | otherwise -> raise (defaultRTErr { _ErrorCause = "The number of arguments of `CI_Pi\' must be 1." })
            (NCon pred, args) -> do
                let instantiate = instantiate_aux . unfoldlNApp . rewrite HNF
                    instantiate_aux (NCon (Atom { _ID = CI_Lambda }), args)
                        | [fact1] <- args = do
                            uni <- liftIO newUnique
                            let v = mkTypeAtom (VI_Unique uni)
                            modify (enterID v (_Scope ctx))
                            instantiate (mkNApp fact1 (mkLVar v))
                        | otherwise = raise (defaultRTErr { _ErrorCause = "The number of arguments of `CI_Lambda\' must be 1." })
                    instantiate_aux (NCon (Atom { _ID = CI_If }), args)
                        | [conclusion, premise] <- args = return (conclusion, premise)
                        | otherwise = raise (defaultRTErr { _ErrorCause = "The number of arguments of `CI_If\' must be 2." })
                    instantiate_aux (NCon (Atom { _ID = CI_Pi }), args)
                        | [fact1] <- args = do
                            uni <- liftIO newUnique
                            let v = mkTermAtom (VI_Unique uni)
                            modify (enterID v (_Scope ctx))
                            instantiate (mkNApp fact1 (mkLVar v))
                        | otherwise = raise (defaultRTErr { _ErrorCause = "The number of arguments of `CI_Pi\' must be 1." })
                    instantiate_aux (NCon (Atom { _ID = CI_True }), args) = raise (defaultRTErr { _ErrorCause = "`CI_True\' cannot be head of fact." })
                    instantiate_aux (NCon (Atom { _ID = CI_Fail }), args) = raise (defaultRTErr { _ErrorCause = "`CI_Fail\' cannot be head of fact." })
                    instantiate_aux (NCon (Atom { _ID = CI_Cut }), args) = raise (defaultRTErr { _ErrorCause = "`CI_Cut\' cannot be head of fact." })
                    instantiate_aux (NCon (Atom { _ID = CI_And }), args) = raise (defaultRTErr { _ErrorCause = "`CI_And\' cannot be head of fact." })
                    instantiate_aux (NCon (Atom { _ID = CI_Or }), args) = raise (defaultRTErr { _ErrorCause = "`CI_Or\' cannot be head of fact." })
                    instantiate_aux (NCon (Atom { _ID = CI_Imply }), args) = raise (defaultRTErr { _ErrorCause = "`CI_Imply\' cannot be head of fact." })
                    instantiate_aux (NCon (Atom { _ID = CI_Sigma }), args) = raise (defaultRTErr { _ErrorCause = "`CI_Sigma\' cannot be head of fact." })
                    instantiate_aux (NCon c, args) = return (List.foldl' mkNApp (mkNCon c) args, mkNCon (mkTermAtom CI_True))
                dummy' <- fmap concat $ forM facts $ \fact -> do
                    let failure = return []
                        success (ctx, goal) = return [Proves ctx goal]
                    ((conclusion, premise), labeling) <- lift (runStateT (instantiate (zonk fact)) (_Label ctx))
                    case unfoldlNApp (rewrite HNF conclusion) of
                        (NCon pred', args')
                            | pred == pred' -> do
                                let disagreements = zipWith Disagreement args args' ++ _Lefts ctx
                                    disagreements_are_zonked = True
                                output <- liftIO (runHOPU disagreements labeling)
                                case output of
                                    Nothing -> failure
                                    Just (HopuEnv labeling' binding', disagreements') -> success
                                        ( ctx
                                            { _Label = labeling'
                                            , _Subst = binding'
                                            , _Lefts = disagreements'
                                            }
                                        , premise
                                        )
                        _ -> failure
                put (hypotheses, dummy : stack)
                transit dummy'
            _ -> raise (defaultRTErr { _ErrorCause = "Every head of any goal must be a constant." })
    transit (Discharge uni : dummy) = do
        (hypotheses, stack) <- get
        put (Map.delete uni hypotheses, stack)
        transit dummy
    go :: Goal -> IO Satisfied
    go goal = loop Map.empty [Proves initCtx goal] [] where
        initCtx :: Context
        initCtx = Context
            { _Scope = 0
            , _Subst = mempty
            , _Label = Labeling
                { _VarLabel = Map.empty
                , _ConLabel = Map.empty
                }
            , _Lefts = []
            }
        loop :: Map.Map Unique Fact -> Dummy -> Stack -> IO Satisfied
        loop hypotheses dummy stack
            | null dummy && null stack = return "-no"
            | otherwise = do
                output <- runExceptT (runStateT (transit dummy) (hypotheses, []))
                case output of
                    Left err -> do
                        print err
                        return "-err"
                    Right ((Nothing, dummy'), (hypotheses', stack')) -> loop hypotheses' dummy' stack'
                    Right ((Just ctx, dummy'), (hypotheses', stack')) -> do
                        more <- answer ctx
                        if more
                            then loop hypotheses' dummy' stack'
                            else return "-yes"
