module Aladdin.Back.Kernel.Runtime where

import Aladdin.Back.Base.Labeling
import Aladdin.Back.Base.TermNode
import Aladdin.Back.Base.TermNode.Util
import Aladdin.Back.Base.VarBinding
import Aladdin.Back.Kernel.KernelErr
import Aladdin.Back.Kernel.Runtime.Transition
import Aladdin.Back.Kernel.Runtime.Util
import Control.Monad.IO.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.State.Strict

initialContext :: Context
initialContext = Context
    { _TotalVarBinding = mempty
    , _CurrentLabeling = theEmptyLabeling
    , _LeftConstraints = []
    }

execRuntime :: RuntimeEnv -> [Fact] -> Goal -> ExceptT KernelErr IO Satisfied
execRuntime env program query = runTransition env [(initialContext, [Cell program 0 query])] []
