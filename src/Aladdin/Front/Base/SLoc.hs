module Aladdin.Front.Base.SLoc where

import Lib.Base

type SPos = (Int, Int)

data SLoc
    = SLoc
        { _FirstPos :: SPos
        , _LastPos :: SPos
        }
    deriving (Eq)

instance Show SLoc where
    showList = undefined
    showsPrec _ (SLoc (row1, col1) (row2, col2)) = strstr "(" . showsPrec 0 row1 . strstr ", " . showsPrec 0 col1 . strstr ") - (" . showsPrec 0 row2 . strstr ", " . showsPrec 0 col2 . strstr ")"

instance Semigroup SLoc where
    loc1 <> loc2 = SLoc
        { _FirstPos = min (_FirstPos loc1) (_FirstPos loc2)
        , _LastPos = max (_LastPos loc1) (_LastPos loc2)
        }
