module Aladdin.Back.Base.Labeling where

import Aladdin.Back.Base.Constant
import Aladdin.Back.Base.TermNode
import Aladdin.Back.Base.TermNode.Util
import Aladdin.Back.Base.VarBinding
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

type ScopeLevel = Int

data Labeling
    = Labeling
        { _ConLabel :: Map.Map Constant ScopeLevel
        , _VarLabel :: Map.Map LogicVar ScopeLevel
        }
    deriving ()

class Labelable atom where
    enrollLabel :: atom -> ScopeLevel -> Labeling -> Labeling
    updateLabel :: atom -> ScopeLevel -> Labeling -> Labeling
    lookupLabel :: atom -> Labeling -> ScopeLevel

instance Labelable Constant where
    enrollLabel atom level labeling = labeling { _ConLabel = Map.insert atom level (_ConLabel labeling) }
    updateLabel atom level labeling = labeling { _ConLabel = Map.insert atom level (_ConLabel labeling) }
    lookupLabel atom labeling = maybe 0 id (Map.lookup atom (_ConLabel labeling))

instance Labelable LogicVar where
    enrollLabel atom level labeling = labeling { _VarLabel = Map.insert atom level (_VarLabel labeling) }
    updateLabel atom level labeling = labeling { _VarLabel = Map.insert atom level (_VarLabel labeling) }
    lookupLabel atom labeling = maybe 0 id (Map.lookup atom (_VarLabel labeling))

instance ZonkLVar Labeling where
    zonkLVar theta labeling = labeling { _VarLabel = Map.mapWithKey loop (_VarLabel labeling) } where
        loop :: LogicVar -> ScopeLevel -> ScopeLevel
        loop v label = foldr min label
            [ label'
            | (v', t') <- Map.toList (unVarBinding theta)
            , v `Set.member` getFreeLVs t'
            , label' <- fromMaybeToList (Map.lookup v' (_VarLabel labeling))
            ]

fromMaybeToList :: Maybe a -> [a]
fromMaybeToList Nothing = []
fromMaybeToList (Just x) = [x]

theEmptyLabeling :: Labeling
theEmptyLabeling = Labeling
    { _ConLabel = Map.empty
    , _VarLabel = Map.empty
    }
