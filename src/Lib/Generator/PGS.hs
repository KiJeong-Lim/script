module Lib.Generator.PGS where

import Control.Applicative
import Control.Monad
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.State.Strict
import Control.Monad.Trans.Writer.Strict
import Data.Functor.Identity
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Lib.Base
import Lib.Generator.PGS.Read
import Lib.Generator.PGS.Show
import Lib.Generator.PGS.Util
import Lib.Text.PC
import Lib.Text.PC.Expansion

runPGS :: FilePath -> IO ()
runPGS dir = do
    y_src <- readFile dir
    case runPC (many (readBlock <* many lend)) y_src of
        Left err -> putStrLn err
        Right yblocks -> case runIdentity (runExceptT (genParser yblocks)) of
            Left err -> putStrLn err
            Right delta -> do
                writeFile (dir ++ ".hs") (delta "")
                putStrLn "the parser has been generated."
                return ()
