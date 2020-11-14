module Aladdin.Back.Kernel.HOPU where

import Aladdin.Back.Base.Labeling
import Aladdin.Back.Base.TermNode
import Aladdin.Back.Base.TermNode.Util
import Aladdin.Back.Base.VarBinding
import Aladdin.Back.Kernel.Disagreement
import Aladdin.Back.Kernel.HOPU.Bind
import Aladdin.Back.Kernel.HOPU.MkSubst
import Aladdin.Back.Kernel.HOPU.Select
import Aladdin.Back.Kernel.HOPU.Simplify
import Aladdin.Back.Kernel.HOPU.Util
import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.State.Strict
import Data.IORef

runHOPU :: Labeling -> [Disagreement] -> IO (Maybe ([Disagreement], HopuSol))
runHOPU labeling disagreements = do
    changed <- newIORef False
    let sol = HopuSol { _SolLabeling = labeling, _SolVBinding = mempty }
        loop disagreements = do
            disagreements' <- simplify changed disagreements
            has_changed <- liftIO (readIORef changed)
            if has_changed
                then do
                    liftIO (writeIORef changed False)
                    loop disagreements'
                else return disagreements'
    output <- runExceptT (runStateT (loop disagreements) sol)
    case output of
        Left err -> return Nothing
        Right result -> return (Just result)
