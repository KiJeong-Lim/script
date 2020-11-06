module Lib.Base where

import Control.Applicative
import Control.Monad

type Indentation = Int

newtype PM output
    = PM { runPM :: String -> [(output, String)] }
    deriving ()

instance Functor PM where
    fmap a2b fa = PM $ \str -> [ (a2b a, str') | (a, str') <- fa `runPM` str ]
    a <$ fb = PM $ \str -> [ (a, str') | (b, str') <- fb `runPM` str ]

instance Applicative PM where
    pure a = PM $ \str -> [(a, str)]
    fa2b <*> fa = PM $ \str -> [ (a2b a, str'') | (a2b, str') <- fa2b `runPM` str, (a, str'') <- fa `runPM` str' ]
    fa *> fb = PM $ \str -> [ (b, str'') | (a, str') <- fa `runPM` str, (b, str'') <- fb `runPM` str' ]
    fa <* fb = PM $ \str -> [ (a, str'') | (a, str') <- fa `runPM` str, (b, str'') <- fb `runPM` str' ]

instance Alternative PM where
    empty = PM $ \str -> []
    fa <|> fa' = PM $ \str -> fa `runPM` str ++ fa' `runPM` str
    many fa = PM $ \str -> some fa `runPM` str ++ [([], str)]
    some fa = PM $ \str -> [ (a : as, str'') | (a, str') <- fa `runPM` str, (as, str'') <- many fa `runPM` str' ]

instance Monad PM where
    return = PM . curry return
    ma >>= a2mb = PM (flip (>>=) (uncurry (runPM . a2mb)) . runPM ma)
    (>>) = (*>)

instance MonadPlus PM where
    mzero = PM (pure mzero)
    mplus ma ma' = PM (pure mplus <*> runPM ma <*> runPM ma')

instance MonadFail PM where
    fail = PM . const . fail

instance Semigroup (PM a) where
    p1 <> p2 = p1 <|> p2

instance Monoid (PM a) where
    mempty = empty

strstr :: String -> String -> String
strstr str1 str2 = str1 ++ str2

strcat :: [String -> String] -> String -> String
strcat = foldr (.) id

nl :: String -> String
nl str = "\n" ++ str

pindent :: Indentation -> String -> String
pindent space str1
    | space < 0 = str1
    | otherwise = replicate space ' ' ++ str1

plist :: Indentation -> [String -> String] -> String -> String
plist space [] = strstr "[]"
plist space (delta : deltas) = nl . pindent space . strstr "[ " . loop delta deltas where
    loop :: (String -> String) -> [String -> String] -> String -> String
    loop delta1 [] = strcat
        [ delta . nl
        , pindent space . strstr "]"
        ]
    loop delta1 (delta2 : deltas) = strcat
        [ delta1 . nl
        , pindent space . strstr ", " . loop delta2 deltas
        ]
