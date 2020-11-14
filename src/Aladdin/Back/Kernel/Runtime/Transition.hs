module Aladdin.Back.Kernel.Runtime.Transition where

import Aladdin.Back.Base.Constant
import Aladdin.Back.Base.Labeling
import Aladdin.Back.Base.TermNode
import Aladdin.Back.Base.TermNode.Util
import Aladdin.Back.Base.VarBinding
import Aladdin.Back.Kernel.Constraint
import Aladdin.Back.Kernel.Disagreement
import Aladdin.Back.Kernel.HOPU
import Aladdin.Back.Kernel.HOPU.Util
import Aladdin.Back.Kernel.KernelErr
import Aladdin.Back.Kernel.Reducer.Util
import Aladdin.Back.Kernel.Runtime.Instantiation
import Aladdin.Back.Kernel.Runtime.LogicalOperator
import Aladdin.Back.Kernel.Runtime.Util
import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.State.Strict

runTransition :: RuntimeEnv -> Stack -> [Stack] -> ExceptT KernelErr IO Satisfied
runTransition env = go where
    searchStarStar :: [Fact] -> ScopeLevel -> DataConstructor -> [TermNode] -> Context -> [Cell] -> Stack -> ExceptT KernelErr IO Stack
    searchStarStar facts level pred args ctx cells stack = do
        solutions <- _Reduce env facts (Statement pred args) (_LeftConstraints ctx) (_CurrentLabeling ctx)
        fmap concat $ sequence
            [ case (applyBinding subst facts, subst <> _TotalVarBinding ctx) of
                (facts', binding') -> fmap concat $ forM facts' $ \fact' -> do
                    let failure = return []
                        success with = return [with]
                    ((goal', new_goal), labeling') <- runStateT (instantiateFact fact' level) labeling
                    case unfoldlNApp (rewrite HNF goal') of
                        (NCon (DC pred'), args')
                            | pred == pred' -> do
                                hopu_ouput <- if length args == length args'
                                    then liftIO (runHOPU labeling' ([ lhs :=?=: rhs | (lhs, rhs) <- zip args args' ] ++ [ disagreement | Disagreement disagreement <- constraints ]))
                                    else throwE (BadFactGiven goal')
                                case hopu_ouput of
                                    Nothing -> failure
                                    Just (disagreements', HopuSol new_labeling subst') -> success
                                        ( Context
                                            { _TotalVarBinding = subst' <> binding'
                                            , _CurrentLabeling = new_labeling
                                            , _LeftConstraints = concat
                                                [ map Disagreement disagreements'
                                                , [ Statement pred'' (applyBinding subst' args'') | Statement pred'' args'' <- constraints ]
                                                ]
                                            }
                                        , zonkLVar subst' (Cell facts' level new_goal) : map (zonkLVar (subst' <> subst)) cells
                                        )
                        _ -> failure
            | Solution labeling subst constraints <- solutions
            ]
    loop :: Context -> [Fact] -> ScopeLevel -> (TermNode, [TermNode]) -> [Cell] -> Stack -> [Stack] -> ExceptT KernelErr IO Satisfied
    loop ctx facts level (NCon key, args) cells stack stacks
        | LO logical_operator <- key
        = do
            stack' <- runLogicalOperator logical_operator args ctx facts level cells stack
            go stack' stacks
        | DC DC_eq <- key = case args of
            [typ, lhs, rhs] -> do
                solutions <- _Reduce env facts (Disagreement (lhs :=?=: rhs)) (_LeftConstraints ctx) (_CurrentLabeling ctx)
                go ([ (Context (subst <> _TotalVarBinding ctx) labeling constraints, map (zonkLVar subst) cells) | Solution labeling subst constraints <- solutions ] ++ stack) stacks
            _ -> throwE (BadGoalGiven (foldlNApp (mkNCon key) args))
        | DC pred <- key
        = do
            stack' <- searchStarStar facts level pred args ctx cells stack
            go stack' (stack : stacks)
    loop ctx facts level (t, ts) cells stack stacks = throwE (BadGoalGiven (foldlNApp t ts))
    go :: Stack -> [Stack] -> ExceptT KernelErr IO Satisfied
    go [] [] = return False
    go [] (stack : stacks) = go stack stacks
    go ((ctx, cells) : stack) stacks = do
        liftIO (_PutStr env (showsCurrentState ctx cells stack ""))
        case cells of
            [] -> do
                want_more <- liftIO (_Answer env ctx)
                if want_more
                    then go stack stacks
                    else return True
            Cell facts level goal : cells' -> loop ctx facts level (unfoldlNApp (rewrite HNF goal)) cells' stack stacks
