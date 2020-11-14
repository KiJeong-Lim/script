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

instance ZonkLVar HopuSol where
    zonkLVar theta (HopuSol labeling binding) = HopuSol (zonkLVar theta labeling) (zonkLVar theta binding)

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
