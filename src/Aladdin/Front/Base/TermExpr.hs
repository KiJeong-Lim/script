module Aladdin.Front.Base.TermExpr where

import Aladdin.Front.Base.ID

data Literal
    = StrLit String
    | ChrLit Char
    | NatLit Integer
    deriving (Eq, Show)

data TermExpr tapp annot
    = IVar annot IVar
    | DCon annot SmallId tapp 
    | IApp annot (TermExpr tapp annot) (TermExpr tapp annot)
    | IAbs annot IVar (TermExpr tapp annot)
    deriving ()

instance Functor (TermExpr tapp) where
    fmap modify (IVar annot var) = IVar (modify annot) var
    fmap modify (DCon annot con tapp) = DCon (modify annot) con tapp
    fmap modify (IApp annot term1 term2) = IApp (modify annot) (fmap modify term1) (fmap modify term2)
    fmap modify (IAbs annot var term) = IAbs (modify annot) var (fmap modify term)
