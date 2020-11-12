module Aladdin.Back.Kernel.Runtime where

import Aladdin.Back.Base.Constant
import Aladdin.Back.Base.Identifier
import Aladdin.Back.Base.TermNode
import Aladdin.Back.Base.UniqueSymbol
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

type Satisfied = Bool

type Fact = TermNode

type Goal = TermNode

type Stack = [(Context, [Cell])]

data Context
    = Context
        { _AnswerSubst :: VarBinding
        , _LabelingEnv :: Labeling
        , _Constraints :: [Constraint]
        }
    deriving ()

data Cell
    = Cell
        { _LocalFacts :: [Fact]
        , _ScopeLevel :: ScopeLevel
        , _WantedGoal :: Goal
        }
    deriving ()

data Solution
    = Solution
        { _SOL_Subst :: VarBinding
        , _sOL_Label :: Labeling
        }
    deriving ()

data RuntimeEnv
    = RuntimeEnv
        { _PutStr :: String -> IO ()
        , _Answer :: Context -> IO Satisfied
        , _Solver :: [Fact] -> ScopeLevel -> Labeling -> [Constraint] -> EnvUS (ExceptT RuntimeErr IO) [(Solution, [Constraint])]
        , _Evaler :: TermNode -> TermNode -> [Fact] -> ScopeLevel -> Labeling -> [Constraint] -> EnvUS (ExceptT Runtime IO) TermNode
        }
    deriving ()

runTransition :: RuntimeEnv -> Stack -> [Stack] -> EnvUS (ExceptT RuntimeErr IO) Satisfied
runTransition (Runtime put_string print_answer solve_constraints evaluate_term) = go where
    go :: Stack -> [Stack] -> EnvUS (ExceptT RuntimeErr IO) Satisfied
    go [] [] = return False
    go [] (stack : stacks) = go stack stacks
    go ((ctx, cells) : stack) stacks = do
        liftIO (put_string (showsCurrentState ctx cells stack stacks ""))
        case cells of
            [] -> do
                want_more <- print_answer ctx
                if want_more
                    then go stack stacks
                    else return True
            Cell local_facts scope_level wanted_goal : cells' -> case unfoldlNapp (rewrite HNF wanted_goal) of
                (NCon (C_LO logical_operator), args) -> do
                    stack' <- runLogicalOperator logical_operator args local_facts scope_level ctx cells' stack
                    go stack' stacks
                (NCon (C_DC (DC_BuiltIn built_in)), args) -> case built_in of
                    BI_equal
                        | [typ, lhs, rhs] -> do
                            pairs <- solve_constraints local_facts scope_level (_LabelingEnv ctx) (Disagreement (lhs :=?=: rhs) : _Constraints ctx)
                            go ([ (Context (binding' <> _AnswerSubst ctx) labeling' disagreements', applyVarBinding binding' cells') | (Solution binding' labeling', disagreements') <- pairs ] ++ stack) stacks
                    BI_is_var
                        | [typ, arg] -> case rewrite NF arg of
                            LVar _ -> go ((ctx, cells') : stack) stacks
                            _ -> go stack stacks
                    BI_assert
                        | [arg] -> do
                            arg' <- makeConstraint arg
                            go ((ctx { _Constraints = arg' : _Constraints ctx }, cells') : stack) stacks
                    BI_check
                        | [typ, arg] -> do
                            arg' <- evaluate_term typ arg local_facts scope_level (_LabelingEnv ctx) (_Constraints ctx)
                            liftIO (put_string (showsPrec 0 arg (" : " ++ showsPrec 0 typ (" = " ++ showsPrec 0 arg' "."))))
                            go ((ctx, cells) : stack) stacks
                    _ -> throwE (makeRuntimeError (BadGoalGiven wanted_goal))
                (NCon predicate, args) -> do
                    stack' <- fmap concat $ forM local_facts $ \fact -> do
                        ((conclusion, premise), labeling) <- runStateT (instantiateFact fact scope_level) (_LabelingEnv ctx)
                        case unfoldlNapp (rewrite HNF conclusion) of
                            (NCon predicate', args')
                                | predicate == predicate' -> do
                                    pairs <- if length args == length args'
                                        then solve_constraints local_facts scope_level (_LabelingEnv ctx) ([ Disagreement (lhs :=?=: rhs) | (lhs, rhs) <- zip args args' ] ++ _Constraints ctx)
                                        else throwE (makeRuntimeError (ArgNumNotMatched (length args) (length args')))
                                    return [ (Context (binding' <> _AnswerSubst ctx) labeling' disagreements', applyVarBinding binding' (Cell local_facts scope_level premise : cells')) | (Solution binding' labeling', disagreements') <- pairs ]
                            _ -> return []
                    go stack' (stack : stacks)
                _ -> throwE (makeRuntimeError (BadGoalGiven wanted_goal))

execRuntime :: RuntimeEnv -> [Fact] -> Goal -> EnvUS (ExceptT RuntimeErr IO) Satisfied
execRuntime env program query = runTransition env [(initContext, [Cell program 0 query])] where
    initContext :: Context
    initContext = Context
        { _AnswerSubst = mempty
        , _LabelingEnv = theEmptyLabeling
        , _Constraints = []
        }
