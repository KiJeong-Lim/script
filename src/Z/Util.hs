module Z.Util where

import Control.Applicative
import Control.Monad

type Precedence = Int

type Indentation = Int

newtype PM a
    = PM { unPM :: String -> [(a, String)] }
    deriving ()

class Outputable a where
    pprint :: Precedence -> a -> String -> String

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

instance Semigroup (PM a) where
    m1 <> m2 = m1 <|> m2

instance Monoid (PM a) where
    mempty = empty

autoPM :: Read a => Precedence -> PM a
autoPM = PM . readsPrec

acceptCharIf :: (Char -> Bool) -> PM Char
acceptCharIf condition = PM $ \str -> let ch = head str in if null str then [] else if condition ch then [(ch, tail str)] else []

consumeStr :: String -> PM ()
consumeStr prefix = PM $ \str -> let n = length prefix in if take n str == prefix then return ((), drop n str) else []

matchPrefix :: String -> PM ()
matchPrefix prefix = PM $ \str -> let n = length prefix in if take n str == prefix then return ((), str) else []

pstr :: String -> ShowS
pstr str1 str2 = str1 ++ str2

pcat :: [ShowS] -> ShowS
pcat = foldr (.) id

pnl :: ShowS
pnl str = '\n' : str

pindent :: Indentation -> ShowS
pindent space str1 = if space < 0 then str1 else replicate space ' ' ++ str1

ppunc :: String -> [ShowS] -> ShowS
ppunc str [] = id
ppunc str (delta1 : deltas2) = delta1 . foldr (\delta2 -> \acc -> pstr str . delta2 . acc) id deltas2

plist :: Indentation -> [ShowS] -> ShowS
plist space [] = pstr "[]"
plist space (delta : deltas) = pnl . pindent space . pstr "[ " . loop delta deltas where
    loop :: ShowS -> [ShowS] -> ShowS
    loop delta1 [] = delta1 . pnl . pindent space . pstr "]"
    loop delta1 (delta2 : deltas3) = delta1 . pnl . pindent space . pstr ", " . loop delta2 deltas3

split' :: (a -> a -> Bool) -> [a] -> [[a]]
split' cond (x1 : x2 : xs)
    | cond x1 x2 = case split' cond (x2 : xs) of
        y : ys -> (x1 : y) : ys
split' cond [] = []
split' cond (x1 : xs) = [x1] : split' cond xs
