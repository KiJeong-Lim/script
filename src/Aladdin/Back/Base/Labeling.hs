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

fromMaybeToList :: Maybe a -> [a]
fromMaybeToList Nothing = []
fromMaybeToList (Just x) = [x]
