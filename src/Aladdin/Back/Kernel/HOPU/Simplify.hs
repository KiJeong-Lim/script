module Aladdin.Back.Kernel.HOPU.Simplify where

import Aladdin.Back.Base.Labeling
import Aladdin.Back.Base.TermNode
import Aladdin.Back.Base.TermNode.Util
import Aladdin.Back.Base.VarBinding
import Aladdin.Back.Kernel.Disagreement
import Aladdin.Back.Kernel.HOPU.Bind
import Aladdin.Back.Kernel.HOPU.MkSubst
import Aladdin.Back.Kernel.HOPU.Select
import Aladdin.Back.Kernel.HOPU.Util
import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.State.Strict
import Data.IORef
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Unique

type SolutionChanged = Bool

simplify :: IORef SolutionChanged -> [Disagreement] -> StateT HopuSol (ExceptT HopuFail IO) [Disagreement]
simplify changed = loop where
    insert' :: Eq a => a -> [a] -> [a]
    insert' x xs
        | null xs = x : xs
        | x == head xs = xs
        | otherwise = head xs : insert' x (tail xs)
    loop :: [Disagreement] -> StateT HopuSol (ExceptT HopuFail IO) [Disagreement]
    loop [] = return []
    loop (lhs :=?=: rhs : disagreements) = go (rewrite HNF lhs) (rewrite HNF rhs) where
        solveNext :: StateT HopuSol (ExceptT HopuFail IO) [Disagreement]
        solveNext = do
            disagreements' <- loop disagreements
            sol <- get
            return (insert' (applyBinding (_MostGeneralUnifier sol) (lhs :=?=: rhs)) disagreements)
        go :: TermNode -> TermNode -> StateT HopuSol (ExceptT HopuFail IO) [Disagreement]
        go lhs rhs
            | (lambda1, lhs') <- viewNestedNAbs lhs
            , (lambda2, rhs') <- viewNestedNAbs rhs
            , lambda1 > 0 && lambda2 > 0
            = case lambda1 `compare` lambda2 of
                LT -> go lhs' (makeNestedNAbs (lambda2 - lambda1) rhs')
                EQ -> go lhs' rhs'
                GT -> go (makeNestedNAbs (lambda1 - lambda2) lhs') rhs'
            | (lambda1, lhs') <- viewNestedNAbs lhs
            , (rhs_head, rhs_tail) <- unfoldlNApp rhs
            , lambda1 > 0 && isRigid rhs_head
            = go lhs' (foldlNApp rhs (map mkNIdx [lambda1, lambda1 - 1 .. 1]))
            | (lhs_head, lhs_tail) <- unfoldlNApp lhs
            , (lambda2, rhs') <- viewNestedNAbs rhs
            , isRigid lhs_head && lambda2 > 0
            = go (foldlNApp lhs (map mkNIdx [lambda2, lambda2 - 1 .. 1])) rhs'
            | (lhs_head, lhs_tail) <- unfoldlNApp lhs
            , (rhs_head, rhs_tail) <- unfoldlNApp rhs
            , isRigid lhs_head && isRigid rhs_head
            = if lhs_head == rhs_head && length lhs_tail == length rhs_tail
                then loop ([ lhs :=?=: rhs | (lhs, rhs) <- zip lhs_tail rhs_tail ] ++ disagreements)
                else lift (throwE RigidRigidFail)
            | (LVar var, parameters) <- unfoldlNApp lhs
            = do
                sol <- get
                output <- lift (mksubst var rhs parameters sol)
                case output of
                    Nothing -> solveNext
                    Just sol -> do
                        put sol
                        liftIO (writeIORef changed True)
                        loop (applyBinding (_MostGeneralUnifier sol) disagreements)
            | (LVar var, parameters) <- unfoldlNApp rhs
            = do
                sol <- get
                output <- lift (mksubst var lhs parameters sol)
                case output of
                    Nothing -> solveNext
                    Just sol -> do
                        put sol
                        liftIO (writeIORef changed True)
                        loop (applyBinding (_MostGeneralUnifier sol) disagreements)
            | otherwise
            = solveNext
