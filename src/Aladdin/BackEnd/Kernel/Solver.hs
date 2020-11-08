module Aladdin.BackEnd.Kernel.Solver where

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

neg :: Int -> Int
neg n = 0 - n

runProver :: Int -> Facts -> Context -> ExceptT String IO (Maybe Context)
runProver = undefined

runSolver :: SolverOption -> Facts -> Context -> ExceptT String IO (Maybe Context)
runSolver PushItToTheLimit = runProver (neg 1)
runSolver (MaxDepth max_dep)
    | max_dep < 0 = pure (pure (throwE ("`max_dep\' must be a natural number.")))
    | otherwise = runProver max_dep
runSolver JustEquations = pure go where
    splitConstraints :: Monad m => [Constraint] -> m ([Disagreement], [Constraint])
    splitConstraints [] = return ([], [])
    splitConstraints (Disagreement disagreement : constraints) = do
        (disagreements, others) <- splitConstraints constraints
        return (disagreement : disagreements, others)
    splitConstraints (constraint : constraints) = do
        (disagreements, others) <- splitConstraints constraints
        return (disagreements, constraint : others)
    go :: Context -> ExceptT String IO (Maybe Context)
    go ctx = do
        (disagreements, others) <- splitConstraints (_Lefts ctx)
        output <- liftIO (runHOPU disagreements (_Label ctx))
        case output of
            Nothing -> return Nothing
            Just (HopuEnv labeling binding, disagreements) -> return (Just (ctx { _Lefts = map Disagreement disagreements ++ others, _Label = labeling, _Subst = binding }))
