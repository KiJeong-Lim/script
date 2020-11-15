module Aladdin.Back.Kernel.HOPU.Bind where

import Aladdin.Back.Base.Labeling
import Aladdin.Back.Base.TermNode
import Aladdin.Back.Base.TermNode.Util
import Aladdin.Back.Base.VarBinding
import Aladdin.Back.Kernel.Disagreement
import Aladdin.Back.Kernel.HOPU.Select
import Aladdin.Back.Kernel.HOPU.Util
import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.State.Strict
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Unique

bind :: LogicVar -> TermNode -> [TermNode] -> Int -> StateT HopuSol (ExceptT HopuFail IO) TermNode
bind var = go . rewrite HNF where
    go :: TermNode -> [TermNode] -> Int -> StateT HopuSol (ExceptT HopuFail IO) TermNode
    go rhs parameters lambda
        | (lambda', rhs') <- viewNestedNAbs rhs
        , lambda' > 0
        = do
            lhs' <- go rhs' parameters (lambda + lambda')
            return (makeNestedNAbs lambda' lhs')
        | (rhs_head, rhs_tail) <- unfoldlNApp rhs
        , isRigid rhs_head
        = do
            sol <- get
            let labeling = _SolLabeling sol
                get_lhs_head lhs_arguments
                    | NCon con <- rhs_head
                    , lookupLabel var labeling >= lookupLabel con labeling
                    = return rhs_head
                    | Just idx <- rhs_head `List.elemIndex` lhs_arguments
                    = return (mkNIdx (length lhs_arguments - idx))
                    | otherwise
                    = lift (throwE FlexRigidFail)
                foldbind [] = return []
                foldbind (rhs_tail_elements : rhs_tail) = do
                    lhs_tail_elements <- bind var rhs_tail_elements parameters lambda
                    sol <- get
                    lhs_tail <- foldbind (applyBinding (_SolVBinding sol) rhs_tail)
                    return (lhs_tail_elements : lhs_tail)
            lhs_head <- get_lhs_head ([ rewriteWithSusp param 0 lambda [] NF | param <- parameters ] ++ map mkNIdx [lambda, lambda - 1 .. 1])
            lhs_tail <- foldbind rhs_tail
            return (foldlNApp lhs_head lhs_tail)
        | (LVar var', rhs_tail) <- unfoldlNApp rhs
        = if var == var'
            then lift (throwE OccursCheckFail)
            else do
                sol <- get
                let labeling = _SolLabeling sol
                    isty = isTypeLVar var
                    lhs_arguments = [ rewriteWithSusp param 0 lambda [] NF | param <- parameters ] ++ map mkNIdx [lambda, lambda - 1 .. 1]
                    rhs_arguments = map (rewrite NF) rhs_tail
                    common_arguments = Set.toList (Set.fromList lhs_arguments `Set.intersection` Set.fromList rhs_arguments)
                if isPatternRespectTo var' rhs_arguments labeling
                    then do
                        (rhs_inner, lhs_inner) <- case lookupLabel var labeling `compare` lookupLabel var' labeling of
                            LT -> do
                                selected_lhs_parameters <- lhs_arguments `up` var'
                                selected_rhs_parameters <- selected_lhs_parameters `down` lhs_arguments
                                return (selected_lhs_parameters, selected_rhs_parameters)
                            geq -> do
                                selected_rhs_parameters <- rhs_arguments `up` var
                                selected_lhs_parameters <- selected_rhs_parameters `down` rhs_arguments
                                return (selected_lhs_parameters, selected_rhs_parameters)
                        rhs_outer <- common_arguments `down` rhs_arguments
                        lhs_outer <- common_arguments `down` lhs_arguments
                        common_head <- getNewLVar isty (lookupLabel var labeling)
                        case var' +-> makeNestedNAbs (length rhs_tail) (foldlNApp common_head (rhs_inner ++ rhs_outer)) of
                            Nothing -> lift (throwE OccursCheckFail)
                            Just theta -> modify (zonkLVar theta)
                        return (foldlNApp common_head (lhs_inner ++ lhs_outer))
                    else lift (throwE NotAPattern)
        | otherwise
        = lift (throwE BindFail)
