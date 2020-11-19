module Aladdin.Front.Base.ID where

import Data.Unique

type SmallId = String

type LargeId = String

type IVar = Unique

type TVar = SmallId

type MetaTVar = Unique
