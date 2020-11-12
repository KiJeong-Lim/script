module Aladdin.Back.Base.UniqueSymbol where

import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.State.Strict
import Lib.Base

newtype EnvUS m a
    = EnvUS { unEnvUS :: StateT Integer m a }
    deriving ()

newtype UniqueSymbol
    = UniqueSymbol { unUniqueSymbol :: Integer }
    deriving (Eq, Ord)

class Monad m => MonadUS m where
    genNewUniqueSymbol :: m UniqueSymbol

instance Functor m => Functor (EnvUS m) where
    fmap a2b = EnvUS . fmap a2b . unEnvUS

instance Monad m => Applicative (EnvUS m) where
    pure = EnvUS . pure
    f1 <*> f2 = EnvUS (unEnvUS f1 <*> unEnvUS f2)

instance Monad m => Monad (EnvUS m) where
    f1 >>= f2 = EnvUS (unEnvUS f1 >>= unEnvUS . f2)

instance MonadIO m => MonadIO (EnvUS m) where
    lift = EnvUS . lift . unEnvUS

instance Monad m => MonadUS (EnvUS m) where
    genNewUniqueSymbol = EnvUS go where
        go :: Monad m => StateT Integer m UniqueSymbol
        go = do
            i <- get
            put (i + 1)
            return (UniqueSymbol i)

instance MonadUS m => MonadUS (ExceptT e m) where
    genNewUniqueSymbol = lift genNewUniqueSymbol

instance MonadUS m => MonadUS (StateT s m) where
    genNewUniqueSymbol = lift genNewUniqueSymbol

instance Show UniqueSymbol where
    show = flip (showsPrec 0) ""
    showList = undefined
    showsPrec _ (UniqueSymbol i) = showsPrec 0 i

runEnvUS :: Monad m => EnvUS m a -> m a
runEnvUS = fmap fst . flip runStateT 1 . unEnvUS
