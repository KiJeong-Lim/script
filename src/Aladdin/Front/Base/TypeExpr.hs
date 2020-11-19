module Aladdin.Front.Base.TypeExpr where

import Aladdin.Back.Base.Constant
import Aladdin.Front.Base.ID
import Aladdin.Front.Base.KindExpr
import qualified Data.Map.Strict as Map
import Lib.Base

type TypeEnv = Map.Map SmallId PolyType

data TCon
    = TCon TypeConstructor KindExpr
    deriving ()

data MonoType tvar
    = TyVar tvar
    | TyCon TCon
    | TyApp (MonoType tvar) (MonoType tvar)
    | TyMTV MetaTVar
    deriving (Eq)

data PolyType
    = Forall [SmallId] (MonoType Int)
    deriving ()

instance Eq TCon where
    TCon tc1 _ == TCon tc2 _ = tc1 == tc2

instance Show TCon where
    showsPrec _ (TCon tc _) = showsPrec 0 tc

mkTyArr :: MonoType tvar -> MonoType tvar -> MonoType tvar
typ1 `mkTyArr` typ2 = TyApp (TyApp (TyCon (TCon TC_arrow (read "* -> * -> *"))) typ1) typ2

mkTyO :: MonoType tvar
mkTyO = TyCon (TCon TC_o (read "*"))

mkTyChr :: MonoType tvar
mkTyChr = TyCon (TCon TC_char (read "*"))

mkTyNat :: MonoType tvar
mkTyNat = TyCon (TCon TC_char (read "*"))

mkTyList :: MonoType tvar -> MonoType tvar
mkTyList typ = TyApp (TyCon (TCon TC_list (read "* -> *"))) typ
