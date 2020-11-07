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

type Dummy = (Facts, Goal)

type Stack = [(Context, [Dummy])]

type Satisfied = Bool

data RTErr
    = RTErr
        { _ErrorCause :: String
        , _CurrentEnv :: (Stack, [Stack])
        }
    deriving ()

data Controller
    = Controller
        { _GetStr :: IO (Maybe String)
        , _PutStr :: String -> IO ()
        , _Answer :: Context -> IO Satisfied
        , _Run_BI :: (BuiltIn, [TermNode]) -> Context -> Facts -> IO Context
        }
    deriving ()

data Context
    = Context
        { _Scope :: ScopeLevel
        , _Subst :: VarBinding
        , _Label :: Labeling
        , _Lefts :: [Disagreement]
        }
    deriving ()

instance Show RTErr where
    show = flip (showsPrec 0) ""
    showList = strcat . map (showsPrec 0)
    showsPrec _ (RTErr { _ErrorCause = error_cause, _CurrentEnv = (item, stack) }) = strcat
        [ strstr error_cause . nl
        , showsCurrentState item stack . nl
        ]

showStack :: Indentation -> Stack -> String -> String
showStack space = strcat . map go where
    go :: (Context, [(Facts, Goal)]) -> String -> String
    go (ctx, dummy) = strcat
        [ pindent space . strstr "- progressings = " . plist (space + 4) [ ppunc ", " (map (showsPrec 0) facts) . strstr " |- " . showsPrec 0 goal | (facts, goal) <- dummy ] . nl
        , pindent space . strstr "- context = Context" . nl
        , pindent (space + 4) . strstr "{ " . strstr "_Scope = " . showsPrec 0 (_Scope ctx) . nl
        , pindent (space + 4) . strstr ", " . strstr "_Subst = " . plist (space + 8) [ showsPrec 0 (LVar v) . strstr " +-> " . showsPrec 0 t | (v, t) <- Map.toList (getVarBinding (_Subst ctx)) ] . nl
        , pindent (space + 4) . strstr ", " . strstr "_Lefts = " . plist (space + 8) [ showsPrec 0 lhs . strstr " =?= " . showsPrec 0 rhs | Disagreement lhs rhs <- _Lefts ctx ] . nl
        , pindent (space + 4) . strstr "} " . nl
        ]

showsCurrentState :: Stack -> [Stack] -> String -> String
showsCurrentState stack1 stacks2 = strcat
    [ strstr "* The top of the stack is:" . nl
    , showStack 4 stack1 . nl
    , strstr "* The rest of the stack is:" . nl
    , strcat
        [ strcat 
            [ pindent 2 . strstr "- [# " . showsPrec 0 i . strstr "]:" . nl
            , showStack 4 stack2 . nl
            ]
        | (i, stack2) <- zip [1, 2 .. length stacks2] stacks2
        ]
    , strstr "--------------------------------" . nl
    ]

runtime :: Controller -> Facts -> Goal -> ExceptT RTErr IO Satisfied
runtime (Controller get_str put_str answer runBuiltIn) = go where
    transition :: Stack -> [Stack] -> ExceptT RTErr IO Satisfied
    transition [] [] = return False
    transition [] (stack : stacks) = transition stack stacks
    transition ((ctx, dummy) : stack) stacks = do
        let zonk = rewrite HNF . flatten (_Subst ctx)
            raise = throwE
            defaultRTErr = RTErr
                { _ErrorCause = "An unknown error occured."
                , _CurrentEnv = (((ctx, dummy) : stack), stacks)
                }
        liftIO (put_str (showsCurrentState ((ctx, dummy) : stack) stacks ""))
        liftIO get_str
        case dummy of
            [] -> do
                more <- liftIO (answer ctx)
                if more then transition stack stacks else return True
            (facts, goal) : dummy -> case unfoldlNApp (zonk goal) of
                (NCon (Atom { _ID = CI_Lambda }), args) -> raise (defaultRTErr { _ErrorCause = "`CI_Lambda\' cannot be head of goal." })
                (NCon (Atom { _ID = CI_If }), args) -> raise (defaultRTErr { _ErrorCause = "`CI_If\' cannot be head of goal." })
                (NCon (Atom { _ID = CI_True }), args)
                    | [] <- args -> transition ((ctx, dummy) : stack) stacks
                    | otherwise -> raise (defaultRTErr { _ErrorCause = "The number of arguments of `CI_True\' must be 0." })
                (NCon (Atom { _ID = CI_Cut }), args)
                    | [] <- args -> transition [(ctx, dummy)] stacks
                    | otherwise -> raise (defaultRTErr { _ErrorCause = "The number of arguments of `CI_Cut\' must be 0." })
                (NCon (Atom { _ID = CI_Fail }), args)
                    | [] <- args -> transition stack stacks
                    | otherwise -> raise (defaultRTErr { _ErrorCause = "The number of arguments of `CI_Fail\' must be 0." })
                (NCon (Atom { _ID = CI_And }), args)
                    | [goal1, goal2] <- args -> transition ((ctx, (facts, goal1) : (facts, goal2) : dummy) : stack) stacks
                    | otherwise -> raise (defaultRTErr { _ErrorCause = "The number of arguments of `CI_And\' must be 2." })
                (NCon (Atom { _ID = CI_Or }), args)
                    | [goal1, goal2] <- args -> transition ((ctx, (facts, goal1) : dummy) : (ctx, (facts, goal2) : dummy) : stack) stacks
                    | otherwise -> raise (defaultRTErr { _ErrorCause = "The number of arguments of `CI_Or\' must be 2." })
                (NCon (Atom { _ID = CI_Imply }), args)
                    | [fact1, goal2] <- args -> transition ((ctx, (fact1 : facts, goal2) : dummy) : stack) stacks
                    | otherwise -> raise (defaultRTErr { _ErrorCause = "The number of arguments of `CI_Imply\' must be 2." })
                (NCon (Atom { _ID = CI_Sigma }), args)
                    | [goal1] <- args -> do
                        uni <- liftIO newUnique
                        let v = mkTermAtom (VI_Unique uni)
                            ctx' = ctx { _Label = enterID v (_Scope ctx) (_Label ctx) }
                        transition ((ctx', (facts, mkNApp goal1 (mkLVar v)) : dummy) : stack) stacks
                    | otherwise -> raise (defaultRTErr { _ErrorCause = "The number of arguments of `CI_Sigma\' must be 1." })
                (NCon (Atom { _ID = CI_Pi }), args)
                    | [goal1] <- args -> do
                        uni <- liftIO newUnique
                        let c = mkTermAtom (CI_Unique uni)
                            ctx' = ctx { _Label = enterID c (_Scope ctx + 1) (_Label ctx), _Scope = _Scope ctx + 1 }
                        transition ((ctx', (facts, mkNApp goal1 (mkNCon c)) : dummy) : stack) stacks
                    | otherwise -> raise (defaultRTErr { _ErrorCause = "The number of arguments of `CI_Pi\' must be 1." })
                (NCon (Atom { _ID = CI_ChrL ch }), args) -> raise (defaultRTErr { _ErrorCause = "A character cannot be head of goal." })
                (NCon (Atom { _ID = CI_NatL n }), args) -> raise (defaultRTErr { _ErrorCause = "A natural number cannot be head of goal." })
                (NCon (Atom { _ID = CI_BuiltIn built_in }), args) -> do
                    ctx' <- liftIO (runBuiltIn (built_in, args) ctx facts)
                    transition ((ctx', dummy) : stack) stacks
                (NCon predicate, args) -> do
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
                        instantiate_aux (NCon (Atom { _ID = CI_ChrL ch }), args) = raise (defaultRTErr { _ErrorCause = "A character cannot be head of fact." })
                        instantiate_aux (NCon (Atom { _ID = CI_NatL n }), args) = raise (defaultRTErr { _ErrorCause = "A natural number cannot be head of fact." })
                        instantiate_aux (NCon (Atom { _ID = CI_BuiltIn built_in }), args) = raise (defaultRTErr { _ErrorCause = "A natural number cannot be head of fact." })
                        instantiate_aux (NCon c, args) = return (List.foldl' mkNApp (mkNCon c) args, mkNCon (mkTermAtom CI_True))
                        raise = lift . throwE
                    stack' <- fmap concat $ forM facts $ \fact -> do
                        let failure = return []
                            success (ctx, dummy) = return [(ctx, dummy)]
                        ((conclusion, premise), labeling) <- runStateT (instantiate (zonk fact)) (_Label ctx)
                        case unfoldlNApp (rewrite HNF conclusion) of
                            (NCon predicate', args')
                                | predicate == predicate' && length args == length args' -> do
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
                                            , (facts, premise) : dummy
                                            )
                            _ -> failure
                    transition stack' (stack : stacks)
                _ -> raise (defaultRTErr { _ErrorCause = "Every head of any goal must be a constant." })
    go :: Facts -> Goal -> ExceptT RTErr IO Satisfied
    go program query = transition [(initCtx, [(program, query)])] [] where
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
