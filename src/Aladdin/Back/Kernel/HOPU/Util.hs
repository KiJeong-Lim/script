module Aladdin.Back.Kernel.HOPU.Util where

import Aladdin.Back.Base.Labeling
import Aladdin.Back.Base.TermNode
import Aladdin.Back.Base.TermNode.Show
import Aladdin.Back.Base.TermNode.Util
import Aladdin.Back.Base.VarBinding
import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.State.Strict
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Unique
import Lib.Base

data Disagreement
    = TermNode :=?=: TermNode
    deriving (Eq)

data HopuSol
    = HopuSol
        { _SolLabeling :: Labeling
        , _SolVBinding :: VarBinding
        }
    deriving ()

data HopuFail
    = DownFail
    | UpFail
    | OccursCheckFail
    | FlexRigidFail
    | RigidRigidFail
    | BindFail
    | NotAPattern
    deriving (Eq)

instance Show Disagreement where
    show = flip (showsPrec 0) ""
    showList = ppunc "\n" . map (showsPrec 0)
    showsPrec _ (lhs :=?=: rhs) = showsPrec 0 lhs . strstr " =?= " . showsPrec 0 rhs

instance HasLVar Disagreement where
    getFreeLVars (lhs :=?=: rhs) = getFreeLVars lhs . getFreeLVars rhs
    applyBinding theta (lhs :=?=: rhs) = applyBinding theta lhs :=?=: applyBinding theta rhs

zonkLVar :: VarBinding -> HopuSol -> HopuSol
zonkLVar theta (HopuSol { _SolLabeling = labeling, _SolVBinding = binding }) = HopuSol { _SolLabeling = labeling', _SolVBinding = binding' } where
    loop :: LogicVar -> ScopeLevel -> ScopeLevel
    loop v label = foldr min label
        [ label'
        | (v', t') <- Map.toList (unVarBinding binding)
        , v `Set.member` getFreeLVs t'
        , label' <- fromMaybeToList (Map.lookup v' (_VarLabel labeling))
        ]
    labeling' :: Labeling
    labeling' = labeling { _VarLabel = Map.mapWithKey loop (_VarLabel labeling) }
    binding' :: VarBinding
    binding' = theta <> binding

viewNestedNAbs :: TermNode -> (Int, TermNode)
viewNestedNAbs = go 0 where
    go :: Int -> TermNode -> (Int, TermNode)
    go n (NAbs t) = go (n + 1) t
    go n t = (n, t)

makeNestedNAbs :: Int -> TermNode -> TermNode
makeNestedNAbs n
    | n == 0 = id
    | n > 0 = makeNestedNAbs (n - 1) . NAbs
    | otherwise = undefined

isRigid :: TermNode -> Bool
isRigid (NCon c) = True
isRigid (NIdx i) = True
isRigid _ = False

areAllDistinct :: Eq a => [a] -> Bool
areAllDistinct [] = True
areAllDistinct (x : xs) = not (elem x xs) && areAllDistinct xs

isPatternRespectTo :: LogicVar -> [TermNode] -> Labeling -> Bool
isPatternRespectTo v ts labeling = and
    [ all isRigid ts
    , areAllDistinct ts
    , and
        [ lookupLabel v labeling < lookupLabel c labeling
        | NCon c <- ts
        ]
    ]

getNewLVar :: MonadIO m => Bool -> ScopeLevel -> StateT HopuSol m TermNode
getNewLVar isty label = do
    uni <- liftIO newUnique
    let sym = if isty then LV_ty_var uni else LV_Unique uni
    sol <- get
    put (sol { _SolLabeling = enrollLabel sym label (_SolLabeling sol) })
    return (mkLVar sym)

isType :: LogicVar -> Bool
isType (LV_ty_var uni) = True
isType (LV_Named name) = False
isType (LV_Unique uni) = False
