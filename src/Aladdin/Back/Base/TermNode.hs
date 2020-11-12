module Aladdin.Back.Base.TermNode where

import Aladdin.Back.Base.Constant
import Aladdin.Back.Base.Identifier
import Aladdin.Back.Base.UniqueSymbol
import Lib.Base

type DeBruijnIndex = Int

type SuspEnv = [SuspItem]

type IsTypeLevel = Bool

data LogicVar
    = LV_type_var UniqueSymbol
    | LV_Unique UniqueSymbol
    | LV_Named String
    deriving (Eq, Ord)

data TermNode
    = LVar LogicVar
    | NCon Constant
    | NIdx DeBruijnIndex
    | NApp TermNode TermNode
    | NAbs TermNode
    | Susp
        { getSuspBody :: TermNode
        , getOL :: Int
        , getNL :: Int
        , getSuspEnv :: SuspEnv
        }
    deriving (Eq, Ord)

data SuspItem
    = Dummy Int
    | Binds TermNode Int
    deriving (Eq, Ord)

data ReduceOption
    = WHNF
    | HNF
    | NF
    deriving (Eq)

class Atom a where
    isTypeLevelAtom :: a -> IsTypeLevel
    fromUS :: IsTypeLevel -> UniqueSymbol -> a

instance Atom Constant where
    isTypeLevelAtom (C_TC type_constructor)
        = True
    isTypeLevelAtom (C_LO logical_operator)
        = case logical_operator of
            LO_ty_pi -> True
            _ -> False
    isTypeLevelAtom (C_DC data_constructor)
        = False
    fromUS True uni = C_TC (TC_Unique uni)
    fromUS False uni = C_DC (DC_Unique uni)

instance Atom LogicVar where
    isTypeLevelAtom (LV_type_var uni) = True
    isTypeLevelAtom (LV_Unique uni) = False
    isTypeLevelAtom (LV_Named name) = False
    fromUS True uni = LV_type_var uni
    fromUS False uni = LV_Unique uni

instance Show LogicVar where
    show = flip (showsPrec 0) ""
    showList = undefined
    showsPrec prec (LV_type_var uni) = strstr "TV_" . showsPrec prec uni
    showsPrec prec (LV_Unique uni) = strstr "V_" . showsPrec prec uni
    showsPrec prec (LV_Named name) = strstr name

mkLVar :: LogicVar -> TermNode
mkLVar v = v `seq` LVar v

mkNCon :: Constant -> TermNode
mkNCon c = c `seq` NCon c

mkNIdx :: DeBruijnIndex -> TermNode
mkNIdx i = i `seq` NIdx i

mkNApp :: TermNode -> TermNode -> TermNode
mkNApp t1 t2 = t1 `seq` t2 `seq` NApp t1 t2

mkNAbs :: TermNode -> TermNode
mkNAbs t = t `seq` NAbs t

mkSusp :: TermNode -> Int -> Int -> SuspEnv -> TermNode
mkSusp t 0 0 [] = t
mkSusp t ol nl (item : env) = t `seq` item `seq` Susp t ol nl (item : env)

mkDummy :: Int -> SuspItem
mkDummy l = l `seq` Dummy l

mkBinds :: TermNode -> Int -> SuspItem
mkBinds t l = t `seq` l `seq` Binds t l

lensForSusp :: (TermNode -> TermNode) -> SuspEnv -> SuspEnv
lensForSusp delta = map go where
    go :: SuspItem -> SuspItem
    go (Dummy l) = mkDummy l
    go (Binds t l) = mkBinds (delta t) l

rewriteWithSusp :: TermNode -> Int -> Int -> SuspEnv -> ReduceOption -> TermNode
rewriteWithSusp (LVar v) ol nl env option
    = mkLVar v
rewriteWithSusp (NCon c) ol nl env option
    = mkNCon c
rewriteWithSusp (NIdx i) ol nl env option
    | i > ol = mkNIdx (i - ol + nl)
    | i >= 1 = case env !! (i - 1) of
        Dummy l -> mkNIdx (nl - l)
        Binds t l -> rewriteWithSusp t 0 (nl - l) [] option
    | otherwise = undefined
rewriteWithSusp (NApp t1 t2) ol nl env option
    = case rewriteWithSusp t1 ol nl env WHNF of
        NAbs (Susp t1' ol1' nl1' (Dummy nl1 : env1'))
            | ol1' > 0 && nl1 + 1 == nl1' -> rewriteWithSusp t1' ol1' nl1 (mkBinds (mkSusp t2 ol nl env) nl1 : env1') option
        NAbs t1' -> rewriteWithSusp t1' 1 0 [mkBinds (mkSusp t2 ol nl env) 0] option
        t1' -> case option of
            NF -> mkNApp (rewriteWithSusp t1' 0 0 [] option) (rewriteWithSusp t2 ol nl env option)
            HNF -> mkNApp (rewriteWithSusp t1' 0 0 [] option) (mkSusp t2 ol nl env)
            WHNF -> mkNApp t1' (mkSusp t2 ol nl env)
rewriteWithSusp (NAbs t1) ol nl env option
    | option == WHNF = mkNAbs (mkSusp t1 (ol + 1) (nl + 1) (mkDummy nl : env))
    | otherwise = mkNAbs (rewriteWithSusp t1 (ol + 1) (nl + 1) (mkDummy nl : env) option)
rewriteWithSusp (Susp t ol nl env) ol' nl' env' option
    | ol == 0 && nl == 0 = rewriteWithSusp t ol' nl' env' option
    | ol' == 0 = rewriteWithSusp t ol (nl + nl') env option
    | otherwise = case rewriteWithSusp t ol nl env option of
        NAbs t'
            | option == WHNF -> mkNAbs (mkSusp t' (ol' + 1) (nl' + 1) (mkDummy nl' : env'))
            | otherwise -> mkNAbs (rewriteWithSusp t' (ol' + 1) (nl' + 1) (mkDummy nl' : env') option)
        t' -> rewriteWithSusp t' ol' nl' env' option

rewrite :: ReduceOption -> TermNode -> TermNode
rewrite option t = rewriteWithSusp t 0 0 [] option

unfoldlNApp :: TermNode -> (TermNode, [TermNode])
unfoldlNApp = flip go [] where
    go :: TermNode -> [TermNode] -> (TermNode, [TermNode])
    go (NApp t1 t2) ts = go t1 (t2 : ts)
    go t ts = (t, ts)
