module Aladdin.Back.Kernel.Reducer.Util where

import Aladdin.Back.Base.Labeling
import Aladdin.Back.Base.TermNode
import Aladdin.Back.Base.VarBinding
import Aladdin.Back.Kernel.KernelErr
import Aladdin.Back.Kernel.Constraint
import Aladdin.Back.Kernel.Disagreement

data Solution
    = Solution
        { _NewLabeling :: Labeling
        , _ResultSubst :: VarBinding
        , _Constraints :: [Constraint]
        }
    deriving ()
