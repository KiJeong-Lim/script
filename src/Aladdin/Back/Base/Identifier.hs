module Aladdin.Back.Base.Identifier where

import Lib.Base

data Associativity
    = A_left
    | A_right
    | A_none
    deriving (Eq, Ord)

data Identifier
    = ID_InfixOperator Associativity Precedence String
    | ID_PrefixOperator Precedence String
    | ID_Name String
    deriving ()

instance Show Associativity where
    showsPrec prec (A_left) = strstr "left-assoc"
    showsPrec prec (A_right) = strstr "right-assoc"
    showsPrec prec (A_none) = strstr "non-assoc"

instance Eq Identifier where
    id1 == id2 = getName id1 == getName id2

instance Ord Identifier where
    id1 `compare` id2 = getName id1 `compare` getName id2

instance Show Identifier where
    showsPrec prec = strstr . getName

getName :: Identifier -> String
getName (ID_InfixOperator _ _ name) = name
getName (ID_PrefixOperator _ name) = name
getName (ID_Name name) = name
