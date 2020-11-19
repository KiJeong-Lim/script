module Aladdin.Front.Base.KindExpr where

import Aladdin.Front.Base.ID
import qualified Data.Map.Strict as Map
import Lib.Base

type KindEnv = Map.Map SmallId KindExpr

data KindExpr
    = Star
    | KArr KindExpr KindExpr
    deriving (Eq)

instance Read KindExpr where
    readsPrec 0 str0 = [ (kin1 `KArr` kin2, str2) | (kin1, ' ' : '-' : '>' : ' ' : str1) <- readsPrec 1 str0, (kin2, str2) <- readsPrec 0 str1 ] ++ readsPrec 1 str0
    readsPrec 1 ('*' : str0) = [(Star, str0)]
    readsPrec 1 ('(' : str0) = [ (kin, str1) | (kin, ')' : str1) <- readsPrec 0 str0 ]
    readList = undefined

instance Show KindExpr where
    showList = undefined
    showsPrec 0 (kin1 `KArr` kin2) = showsPrec 1 kin1 . strstr " -> " . showsPrec 0 kin2
    showsPrec 0 kin1 = showsPrec 1 kin1
    showsPrec 1 Star = strstr "*"
    showsPrec 1 kin1 = showsPrec 2 kin1
    showsPrec _ kin1 = strstr "(" . showsPrec 0 kin1 . strstr ")"
