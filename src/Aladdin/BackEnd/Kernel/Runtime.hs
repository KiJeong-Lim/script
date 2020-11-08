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

type Stack = [(Context, [Probe])]

data RTErr
    = RTErr
        { _ErrorCause :: String
        , _CurrentEnv :: (Stack, [Stack])
        }
    deriving ()

data Probe
    = Probe
        { _Scope :: ScopeLevel
        , _Facts :: Facts
        , _GOAL_ :: Goal
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
    go :: (Context, [Probe]) -> String -> String
    go (ctx, probes) = strcat
        [ pindent space . strstr "- progressings = " . plist (space + 4) [ strstr "?- " . showsPrec 0 goal | Probe scope facts goal <- probes ] . nl
        , pindent space . strstr "- context = Context" . nl
        , pindent (space + 4) . strstr "{ " . strstr "_Subst = " . plist (space + 8) [ showsPrec 0 (LVar v) . strstr " +-> " . showsPrec 0 t | (v, t) <- Map.toList (getVarBinding (_Subst ctx)) ] . nl
        , pindent (space + 4) . strstr ", " . strstr "_Lefts = " . plist (space + 8) [ showsPrec 0 constraint | constraint <- _Lefts ctx ] . nl
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
runtime (Controller get_str put_str answer run_solver run_prover) = go where
    runBuiltIn :: (BuiltIn, [TermNode]) -> Facts -> Context -> ExceptT String IO (Maybe Context)
    runBuiltIn (built_in, args) facts ctx
        = case built_in of
            BI_equal
                | [typ, arg1, arg2] <- args -> return (Just (ctx { _Lefts = Disagreement (arg1 :=?=: arg2) : _Lefts ctx }))
                | otherwise -> throwE ("The number of arguments of `BI_equal\' must be 3.")
            BI_leq -> return (Just (ctx { _Lefts = Statement (mkTermAtom (CI_BuiltIn built_in)) args : _Lefts ctx }))
            BI_geq -> return (Just (ctx { _Lefts = Statement (mkTermAtom (CI_BuiltIn built_in)) args : _Lefts ctx }))
            BI_is_var
                | [typ, arg1] <- args -> case rewrite NF arg1 of
                    LVar v -> return (Just ctx)
                    notLVar -> return Nothing
                | otherwise -> throwE ("The number of arguments of `BI_is_var\' must be 2.")
            BI_check
                | [arg1] <- args -> liftIO (run_prover facts ctx arg1)
                | otherwise -> throwE ("The number of arguments of `BI_check\' must be 1.")
            BI_assert
                | [arg1] <- args -> case unfoldlNApp (rewrite HNF arg1) of
                    (NCon predicate, args)
                        | Atom { _ID = CI_Named str } <- predicate -> return (Just (ctx { _Lefts = Statement predicate args : _Lefts ctx }))
                        | Atom { _ID = CI_Unique uni } <- predicate -> return (Just (ctx { _Lefts = Statement predicate args : _Lefts ctx }))
                    bad_input -> throwE ("Bad input is given to `BI_assert\'.")
                | otherwise -> throwE ("The number of arguments of `BI_assert\' must be 1.")
            not_callable -> throwE ("The built-in operator `" ++ showsPrec 0 not_callable "\' is not callable.")
    transition :: Stack -> [Stack] -> ExceptT RTErr IO Satisfied
    transition [] [] = return False
    transition [] (stack : stacks) = transition stack stacks
    transition ((ctx, probes) : stack) stacks = do
        let zonk = rewrite HNF . flatten (_Subst ctx)
            raise = throwE
            defaultRTErr = RTErr
                { _ErrorCause = "An unknown error occured."
                , _CurrentEnv = (((ctx, probes) : stack), stacks)
                }
        liftIO (put_str (showsCurrentState ((ctx, probes) : stack) stacks ""))
        liftIO get_str
        case probes of
            [] -> do
                more <- liftIO (answer ctx)
                if more then transition stack stacks else return True
            Probe scope facts goal : probes -> case unfoldlNApp (zonk goal) of
                (NCon (Atom { _ID = CI_Lambda }), args) -> raise (defaultRTErr { _ErrorCause = "`CI_Lambda\' cannot be head of goal." })
                (NCon (Atom { _ID = CI_If }), args) -> raise (defaultRTErr { _ErrorCause = "`CI_If\' cannot be head of goal." })
                (NCon (Atom { _ID = CI_True }), args)
                    | [] <- args -> transition ((ctx, probes) : stack) stacks
                    | otherwise -> raise (defaultRTErr { _ErrorCause = "The number of arguments of `CI_True\' must be 0." })
                (NCon (Atom { _ID = CI_Cut }), args)
                    | [] <- args -> transition [(ctx, probes)] stacks
                    | otherwise -> raise (defaultRTErr { _ErrorCause = "The number of arguments of `CI_Cut\' must be 0." })
                (NCon (Atom { _ID = CI_Fail }), args)
                    | [] <- args -> transition stack stacks
                    | otherwise -> raise (defaultRTErr { _ErrorCause = "The number of arguments of `CI_Fail\' must be 0." })
                (NCon (Atom { _ID = CI_And }), args)
                    | [goal1, goal2] <- args -> transition ((ctx, Probe scope facts goal1 : Probe scope facts goal2 : probes) : stack) stacks
                    | otherwise -> raise (defaultRTErr { _ErrorCause = "The number of arguments of `CI_And\' must be 2." })
                (NCon (Atom { _ID = CI_Or }), args)
                    | [goal1, goal2] <- args -> transition ((ctx, Probe scope facts goal1 : probes) : (ctx, Probe scope facts goal2 : probes) : stack) stacks
                    | otherwise -> raise (defaultRTErr { _ErrorCause = "The number of arguments of `CI_Or\' must be 2." })
                (NCon (Atom { _ID = CI_Imply }), args)
                    | [fact1, goal2] <- args -> transition ((ctx, Probe scope (fact1 : facts) goal2 : probes) : stack) stacks
                    | otherwise -> raise (defaultRTErr { _ErrorCause = "The number of arguments of `CI_Imply\' must be 2." })
                (NCon (Atom { _ID = CI_Sigma }), args)
                    | [goal1] <- args -> do
                        uni <- liftIO newUnique
                        let v = mkTermAtom (VI_Unique uni)
                            ctx' = ctx { _Label = enterID v scope (_Label ctx) }
                        transition ((ctx', Probe scope facts (mkNApp goal1 (mkLVar v)) : probes) : stack) stacks
                    | otherwise -> raise (defaultRTErr { _ErrorCause = "The number of arguments of `CI_Sigma\' must be 1." })
                (NCon (Atom { _ID = CI_Pi }), args)
                    | [goal1] <- args -> do
                        uni <- liftIO newUnique
                        let c = mkTermAtom (CI_Unique uni)
                            ctx' = ctx { _Label = enterID c (scope + 1) (_Label ctx) }
                        transition ((ctx', Probe (scope + 1) facts (mkNApp goal1 (mkNCon c)) : probes) : stack) stacks
                    | otherwise -> raise (defaultRTErr { _ErrorCause = "The number of arguments of `CI_Pi\' must be 1." })
                (NCon (Atom { _ID = CI_ChrL ch }), args) -> raise (defaultRTErr { _ErrorCause = "A character cannot be head of goal." })
                (NCon (Atom { _ID = CI_NatL n }), args) -> raise (defaultRTErr { _ErrorCause = "A natural number cannot be head of goal." })
                (NCon (Atom { _ID = CI_BuiltIn built_in }), args) -> do
                    output <- catchE (runBuiltIn (built_in, args) facts ctx) $ \error_cause -> raise (defaultRTErr { _ErrorCause = error_cause })
                    case output of
                        Nothing -> transition stack stacks
                        Just ctx' -> transition ((ctx', probes) : stack) stacks
                (NCon predicate, args) -> do
                    let raise = lift . throwE
                        instantiate = instantiate_aux . unfoldlNApp . rewrite HNF
                        instantiate_aux (NCon (Atom { _ID = CI_Lambda }), args)
                            | [fact1] <- args = do
                                uni <- liftIO newUnique
                                let v = mkTypeAtom (VI_Unique uni)
                                modify (enterID v scope)
                                instantiate (mkNApp fact1 (mkLVar v))
                            | otherwise = raise (defaultRTErr { _ErrorCause = "The number of arguments of `CI_Lambda\' must be 1." })
                        instantiate_aux (NCon (Atom { _ID = CI_If }), args)
                            | [conclusion, premise] <- args = return (conclusion, premise)
                            | otherwise = raise (defaultRTErr { _ErrorCause = "The number of arguments of `CI_If\' must be 2." })
                        instantiate_aux (NCon (Atom { _ID = CI_Pi }), args)
                            | [fact1] <- args = do
                                uni <- liftIO newUnique
                                let v = mkTermAtom (VI_Unique uni)
                                modify (enterID v scope)
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
                    stack' <- fmap concat $ forM facts $ \fact -> do
                        let failure = return []
                            success (ctx, probes) = return [(ctx, probes)]
                        ((conclusion, premise), labeling) <- runStateT (instantiate (zonk fact)) (_Label ctx)
                        case unfoldlNApp (rewrite HNF conclusion) of
                            (NCon predicate', args')
                                | predicate == predicate' && length args == length args' -> do
                                    let constraints = [ Disagreement (lhs :=?=: rhs) | (lhs, rhs) <- zip args args' ] ++ _Lefts ctx
                                        constraints_are_zonkes = True
                                    output <- liftIO (run_solver facts (ctx { _Lefts = constraints, _Label = labeling }))
                                    case output of
                                        Nothing -> failure
                                        Just ctx' -> success (ctx', Probe scope facts premise : probes)
                            _ -> failure
                    transition stack' (stack : stacks)
                _ -> raise (defaultRTErr { _ErrorCause = "Every head of any goal must be a constant." })
    go :: Facts -> Goal -> ExceptT RTErr IO Satisfied
    go program query = transition [(initCtx, [Probe 0 program query])] [] where
        initCtx :: Context
        initCtx = Context
            { _Subst = mempty
            , _Label = Labeling
                { _VarLabel = Map.empty
                , _ConLabel = Map.empty
                }
            , _Lefts = []
            }
