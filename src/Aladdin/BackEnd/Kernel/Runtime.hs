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

type Goal = TermNode

type StackItem = [(Context, Goal)]

type Stack = [StackItem]

type Satisfied = String

type MoreAnswer = Bool

data Context
    = Context
        { _Scope :: ScopeLevel
        , _Facts :: Facts
        , _Subst :: VarBinding
        , _Label :: Labeling
        , _Lefts :: [Disagreement]
        }
    deriving ()

data RTErr
    = RTErr
        { _ErrorCause :: String
        , _CurrentEnv :: (StackItem, Stack)
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

showStackItem :: Indentation -> StackItem -> String -> String
showStackItem space = strcat . map go where
    go :: (Context, Goal) -> String -> String
    go (ctx, goal) = strcat
        [ pindent space . strstr "- goal = " . showsPrec 0 goal . nl
        , pindent space . strstr "- context = Context" . nl
        , pindent (space + 4) . strstr "{ " . strstr "_Scope = " . showsPrec 0 (_Scope ctx) . nl
        , pindent (space + 4) . strstr ", " . strstr "_Facts = " . plist (space + 8) (map (showsPrec 0) (_Facts ctx)) . nl
        , pindent (space + 4) . strstr ", " . strstr "_Subst = " . plist (space + 8) [ showsPrec 0 (LVar v) . strstr " +-> " . showsPrec 0 t | (v, t) <- Map.toList (getVarBinding (_Subst ctx)) ] . nl
        , pindent (space + 4) . strstr ", " . strstr "_Lefts = " . plist (space + 8) [ showsPrec 0 lhs . strstr " =?= " . showsPrec 0 rhs | Disagreement lhs rhs <- _Lefts ctx ] . nl
        , pindent (space + 4) . strstr "} " . nl
        ]

showsCurrentState :: StackItem -> Stack -> String -> String
showsCurrentState item1 stack2 = strcat
    [ strstr "* The top of the stack is:" . nl
    , showStackItem 4 item1 . nl
    , strstr "* The rest of the stack is:" . nl
    , strcat
        [ strcat 
            [ pindent 2 . strstr "- [# " . showsPrec 0 i . strstr "]:" . nl
            , showStackItem 4 item2 . nl
            ]
        | (i, item2) <- zip [1, 2 .. length stack2] stack2
        ]
    , strstr "--------------------------------" . nl
    ]

runtime :: Controller -> Facts -> Goal -> IO Satisfied
runtime (Controller get_str put_str answer) = go where
    raise :: (MonadTrans t, Monad m) => e -> t (ExceptT e m) a
    raise = lift . throwE
    transit :: StackItem -> StateT Stack (ExceptT RTErr IO) (Maybe Context, StackItem)
    transit [] = do
        stack <- get
        case stack of
            [] -> return (Nothing, [])
            item : stack' -> do
                put stack'
                transit item
    transit ((ctx, goal) : item) = do
        stack <- get
        let zonk = rewrite HNF . flatten (_Subst ctx)
            defaultRTErr = RTErr
                { _ErrorCause = "An unknown error occured."
                , _CurrentEnv = (((ctx, goal) : item), stack)
                }
        liftIO (put_str (showsCurrentState ((ctx, goal) : item) stack ""))
        liftIO get_str
        case unfoldlNApp (zonk goal) of
            (NCon (Atom { _ID = CI_Lambda }), args) -> raise (defaultRTErr { _ErrorCause = "`CI_Lambda\' cannot be a head of goal." })
            (NCon (Atom { _ID = CI_If }), args) -> raise (defaultRTErr { _ErrorCause = "`CI_If\' cannot be a head of goal." })
            (NCon (Atom { _ID = CI_True }), args)
                | [] <- args -> return (Just ctx, item)
                | otherwise -> raise (defaultRTErr { _ErrorCause = "The number of arguments of `CI_True\' must be 0." })
            (NCon (Atom { _ID = CI_Cut }), args)
                | [] <- args -> return (Just ctx, [])
                | otherwise -> raise (defaultRTErr { _ErrorCause = "The number of arguments of `CI_Cut\' must be 0." })
            (NCon (Atom { _ID = CI_Fail }), args)
                | [] <- args -> transit item
                | otherwise -> raise (defaultRTErr { _ErrorCause = "The number of arguments of `CI_Fail\' must be 0." })
            (NCon (Atom { _ID = CI_And }), args)
                | [goal1, goal2] <- args -> do
                    output <- transit ((ctx, goal1) : item)
                    case output of
                        (Nothing, item') -> transit item'
                        (Just ctx', item') -> transit ((ctx', goal2) : item')
                | otherwise -> raise (defaultRTErr { _ErrorCause = "The number of arguments of `CI_And\' must be 2." })
            (NCon (Atom { _ID = CI_Or }), args)
                | [goal1, goal2] <- args -> transit ((ctx, goal1) : (ctx, goal2) : item)
                | otherwise -> raise (defaultRTErr { _ErrorCause = "The number of arguments of `CI_Or\' must be 2." })
            (NCon (Atom { _ID = CI_Imply }), args)
                | [fact1, goal2] <- args -> transit ((ctx { _Facts = fact1 : _Facts ctx }, goal2) : item)
                | otherwise -> raise  (defaultRTErr { _ErrorCause = "The number of arguments of `CI_Imply\' must be 2." })
            (NCon (Atom { _ID = CI_Sigma }), args)
                | [goal1] <- args -> do
                    uni <- liftIO newUnique
                    let v = mkTermAtom (VI_Unique uni)
                        ctx' = ctx { _Label = enterID v (_Scope ctx) (_Label ctx) }
                    transit ((ctx', mkNApp goal1 (mkLVar v)) : item)
                | otherwise -> raise (defaultRTErr { _ErrorCause = "The number of arguments of `CI_Sigma\' must be 1." })
            (NCon (Atom { _ID = CI_Pi }), args)
                | [goal1] <- args -> do
                    uni <- liftIO newUnique
                    let c = mkTermAtom (CI_Unique uni)
                        ctx' = ctx { _Label = enterID c (_Scope ctx + 1) (_Label ctx), _Scope = _Scope ctx + 1 }
                    transit ((ctx', mkNApp goal1 (mkNCon c)) : item)
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
                    instantiate_aux (NCon (Atom { _ID = CI_True }), args) = raise (defaultRTErr { _ErrorCause = "`CI_True\' cannot be a head of fact." })
                    instantiate_aux (NCon (Atom { _ID = CI_Fail }), args) = raise (defaultRTErr { _ErrorCause = "`CI_Fail\' cannot be a head of fact." })
                    instantiate_aux (NCon (Atom { _ID = CI_Cut }), args) = raise (defaultRTErr { _ErrorCause = "`CI_Cut\' cannot be a head of fact." })
                    instantiate_aux (NCon (Atom { _ID = CI_And }), args) = raise (defaultRTErr { _ErrorCause = "`CI_And\' cannot be a head of fact." })
                    instantiate_aux (NCon (Atom { _ID = CI_Or }), args) = raise (defaultRTErr { _ErrorCause = "`CI_Or\' cannot be a head of fact." })
                    instantiate_aux (NCon (Atom { _ID = CI_Imply }), args) = raise (defaultRTErr { _ErrorCause = "`CI_Imply\' cannot be a head of fact." })
                    instantiate_aux (NCon (Atom { _ID = CI_Sigma }), args) = raise (defaultRTErr { _ErrorCause = "`CI_Sigma\' cannot be a head of fact." })
                    instantiate_aux (NCon c, args) = return (List.foldl' mkNApp (mkNCon c) args, mkNCon (mkTermAtom CI_True))
                item' <- fmap concat $ forM (_Facts ctx) $ \fact -> do
                    let failure = return []
                        success with = return [with]
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
                put (item : stack)
                transit item'
            _ -> raise (defaultRTErr { _ErrorCause = "Every head of any goal must be a constant." })
    go :: Facts -> Goal -> IO Satisfied
    go facts goal = loop [(initCtx, goal)] [] where
        initCtx :: Context
        initCtx = Context
            { _Scope = 0
            , _Facts = facts
            , _Subst = mempty
            , _Label = Labeling
                { _VarLabel = Map.empty
                , _ConLabel = Map.empty
                }
            , _Lefts = []
            }
        loop :: StackItem -> Stack -> IO Satisfied
        loop [] [] = return "-no"
        loop [] (item : stack) = loop item stack
        loop item stack = do
            output <- runExceptT (runStateT (transit item) stack)
            case output of
                Left err -> do
                    print err
                    return "-err"
                Right ((Nothing, item'), stack') -> loop item' stack'
                Right ((Just ctx, item'), stack') -> do
                    more <- answer ctx
                    if more
                        then loop item' stack'
                        else return "-yes"
