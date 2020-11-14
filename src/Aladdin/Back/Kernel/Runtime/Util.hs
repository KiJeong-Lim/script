module Aladdin.Back.Kernel.Runtime.Util where

import Aladdin.Back.Base.Labeling
import Aladdin.Back.Base.TermNode
import Aladdin.Back.Base.VarBinding
import Aladdin.Back.Kernel.Constraint
import Aladdin.Back.Kernel.Disagreement
import Aladdin.Back.Kernel.KernelErr
import Aladdin.Back.Kernel.Solver.Util
import Control.Monad.Trans.Except
import Control.Monad.Trans.State.Strict

type Fact = TermNode

type Goal = TermNode

type Stack = [(Context, [Cell])]

type Satisfied = Bool

data Cell
    = Cell
        { _GivenFacts :: [Fact]
        , _ScopeLevel :: ScopeLevel
        , _WantedGoal :: Goal
        }
    deriving ()

data Context
    = Context
        { _TotalVarBinding :: VarBinding
        , _CurrentLabeling :: Labeling
        , _LeftConstraints :: [Constraint]
        }
    deriving ()

data RuntimeEnv
    = RuntimeEnv
        { _PutStr :: String -> IO ()
        , _Answer :: Context -> IO Satisfied
        , _Reduce :: [Fact] -> [Constraint] -> Labeling -> ExceptT KernelErr IO [Solution]
        }
    deriving ()
