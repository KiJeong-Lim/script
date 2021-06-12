module Z.Text.Ppr where

import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import Data.IORef
import System.IO

infixl 1 <<

type Indent = Int

type Pretty = Bool

data Doc

data DocBuffer
    = DocBuffer 
        { memoryDB :: IORef Doc
        , indentDB :: Indent
        , handleDB :: Handle
        }
    deriving ()

renderDoc :: Pretty -> Doc -> String
renderDoc = undefined

textrm :: String -> Doc
textrm = undefined

flush :: MonadIO m => Pretty -> m DocBuffer -> m ()
flush bePretty buf = do
    b <- buf
    d <- liftIO (readIORef (memoryDB b))
    liftIO (hPutStrLn (handleDB b) (renderDoc bePretty d))

(<<) :: (Show a, MonadIO m) => m DocBuffer -> a -> m DocBuffer
buf << x = buf >>= putDocBuffer (textrm (show x))

makeDoc :: MonadIO m => Handle -> (m DocBuffer -> m a) -> m a
makeDoc h run = liftIO (makeNewDocBuffer h) >>= run . return

putDocBuffer :: MonadIO m => Doc -> DocBuffer -> m DocBuffer
putDocBuffer = undefined

makeNewDocBuffer :: MonadIO m => Handle -> m DocBuffer
makeNewDocBuffer = undefined
