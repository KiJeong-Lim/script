module Aladdin.Back.Kernel.Constraint where

import Aladdin.Back.Base.Constant
import Aladdin.Back.Base.TermNode
import Aladdin.Back.Base.TermNode.Show
import Aladdin.Back.Base.TermNode.Util
import Aladdin.Back.Base.VarBinding
import Aladdin.Back.Kernel.Disagreement
import qualified Data.List as List
import Lib.Base

data Constraint
    = Statement DataConstructor [TermNode]
    | Disagreement Disagreement
    deriving (Eq)

instance Show Constraint where
    show = flip (showsPrec 0) ""
    showList = ppunc "\n" . map (showsPrec 0)
    showsPrec prec (Disagreement disagreement) = showsPrec prec disagreement
    showsPrec prec (Statement pred args) = showsPrec prec (foldlNApp (mkNCon (DC pred)) args)

instance HasLVar Constraint where
    getFreeLVars (Disagreement disagreement) = getFreeLVars disagreement
    getFreeLVars (Statement pred args) = getFreeLVars args
    applyBinding theta (Disagreement disagreement) = Disagreement (applyBinding theta disagreement)
    applyBinding theta (Statement pred args) = Statement pred (applyBinding theta args)
