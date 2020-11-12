module Aladdin.Back.Base.Constant where

import Aladdin.Back.Base.Identifier
import Aladdin.Back.Base.UniqueSymbol
import Lib.Base

data LogicalOperator
    = LO_ty_pi
    | LO_if
    | LO_true
    | LO_fail
    | LO_cut
    | LO_and
    | LO_or
    | LO_imply
    | LO_pi
    | LO_sigma
    deriving (Eq, Ord)

data LogicalSymbol
    = LS_contradiction
    | LS_negation
    | LS_conjunction
    | LS_disjunction
    | LS_implication
    | LS_biconditional
    | LS_universal
    | LS_existential
    deriving (Eq, Ord)

data BuiltIn
    = BI_cons
    | BI_nil
    | BI_equal
    | BI_is_var
    | BI_check
    | BI_assert
    | BI_LogicSymbol LogicalSymbol
    deriving (Eq, Ord)

data DataConstructor
    = DC_Named Identifier
    | DC_Unique UniqueSymbol
    | DC_ChrL Char
    | DC_NatL Integer
    | DC_BuiltIn BuiltIn
    deriving (Eq, Ord)

data TypeConstructor
    = TC_Named Identifier
    | TC_Unique UniqueSymbol
    | TC_arrow
    | TC_o
    | TC_list
    | TC_char
    | TC_nat
    deriving (Eq, Ord)

data Constant
    = C_LO LogicalOperator
    | C_DC DataConstructor
    | C_TC TypeConstructor
    deriving (Eq, Ord)

instance Show LogicalOperator where
    show = flip (showsPrec 0) ""
    showList = undefined
    showsPrec prec = strstr . go where
        go :: LogicalOperator -> String
        go LO_ty_pi = "__ty_pi"
        go LO_if = "__if"
        go LO_true = "__true"
        go LO_fail = "__fail"
        go LO_cut = "__cut"
        go LO_and = "__and"
        go LO_or = "__or"
        go LO_imply = "__imply"
        go LO_pi = "__pi"
        go LO_sigma = "__sigma"

instance Show LogicalSymbol where
    show = flip (showsPrec 0) ""
    showList = undefined
    showsPrec _ = strstr . go where
        go :: LogicalSymbol -> String
        go LS_contradiction = "__contradiction"
        go LS_negation = "__negation"
        go LS_conjunction = "__conjunction"
        go LS_disjunction = "__disjunction"
        go LS_implication = "__implication"
        go LS_biconditional = "__biconditional"
        go LS_universal = "__universal"
        go LS_existential = "__existential"

instance Show BuiltIn where
    show = flip (showsPrec 0) ""
    showList = undefined
    showsPrec prec BI_cons = strstr "__cons"
    showsPrec prec BI_nil = strstr "__nil"
    showsPrec prec BI_equal = strstr "__equal"
    showsPrec prec BI_is_var = strstr "__is_var"
    showsPrec prec BI_check = strstr "__check"
    showsPrec prec BI_assert = strstr "__assert"
    showsPrec prec (BI_LogicSymbol logical_symbol) = showsPrec prec logical_symbol

instance Show DataConstructor where
    show = flip (showsPrec 0) ""
    showList = undefined
    showsPrec prec (DC_Named name) = showsPrec 0 name
    showsPrec prec (DC_Unique uni) = strstr "c_" . showsPrec 0 uni
    showsPrec prec (DC_ChrL chr) = showsPrec 0 chr
    showsPrec prec (DC_NatL nat) = showsPrec 0 nat
    showsPrec prec (DC_BuiltIn built_in) = showsPrec prec built_in

instance Show TypeConstructor where
    show = flip (showsPrec 0) ""
    showList = undefined
    showsPrec prec (TC_Named name) = showsPrec 0 name
    showsPrec prec (TC_Unique uni) = strstr "tc_" . showsPrec 0 uni
    showsPrec prec (TC_arrow) = strstr "__arrow"
    showsPrec prec (TC_o) = strstr "__o"
    showsPrec prec (TC_list) = strstr "__list"
    showsPrec prec (TC_char) = strstr "__char"
    showsPrec prec (TC_nat) = strstr "__nat"

instance Show Constant where
    show = flip (showsPrec 0) ""
    showList = undefined
    showsPrec prec (C_LO logical_operator) = showsPrec prec logical_operator
    showsPrec prec (C_DC data_constructor) = showsPrec prec data_constructor
    showsPrec prec (C_TC type_constructor) = showsPrec prec type_constructor
