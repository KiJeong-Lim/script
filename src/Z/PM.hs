module Z.PM where

import Control.Applicative
import Control.Monad

newtype PM a
    = PM { unPM :: String -> [(a, String)] }
    deriving ()

instance Functor PM where
    fmap a2b ma = PM $ \str0 -> do
        (a, str1) <- unPM ma str0
        return (a2b a, str1)

instance Applicative PM where
    pure a = PM $ \str0 -> return (a, str0)
    m1 <*> m2 = PM $ \str0 -> do
        (a2b, str1) <- unPM m1 str0
        (a, str2) <- unPM m2 str1
        return (a2b a, str2)

instance Monad PM where
    return = PM . curry pure
    m1 >>= m2 = PM (flip (>>=) (uncurry (unPM . m2)) . unPM m1)

instance Alternative PM where
    empty = PM (pure [])
    m1 <|> m2 = PM (pure (++) <*> unPM m1 <*> unPM m2)

instance MonadPlus PM where

instance MonadFail PM where
    fail = const empty

autoPM :: Read a => Precedence -> PM a
autoPM = PM . readsPrec

acceptCharIf :: (Char -> Bool) -> PM Char
acceptCharIf condition = PM $ \str -> let ch = head str in if null str then [] else if condition ch then [(ch, tail str)] else []

consumeStr :: String -> PM ()
consumeStr prefix = PM $ \str -> let n = length prefix in if take n str == prefix then return ((), drop n str) else []

matchPrefix :: String -> PM ()
matchPrefix prefix = PM $ \str -> let n = length prefix in if take n str == prefix then return ((), str) else []
