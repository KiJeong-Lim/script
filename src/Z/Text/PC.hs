module Z.Text.PC where

import Control.Applicative
import Control.Monad
import Data.Function
import Test.QuickCheck
import Test.QuickCheck.Checkers
import Z.Algorithm.Sort
import Z.Text.PC.Base
import Z.Text.PC.Loc
import Z.Text.PC.RegEx
import Z.Text.PC.Test

type NameOfPC = String

newtype PC val
    = PC { unPC :: ParserBase LocChr val }
    deriving ()

instance Functor PC where
    fmap a2b = PC . fmap a2b . unPC

instance Applicative PC where
    pure = PC . pure
    p1 <*> p2 = PC (unPC p1 <*> unPC p2)

instance Monad PC where
    p1 >>= p2 = PC (unPC p1 >>= unPC . p2)

instance Alternative PC where
    empty = PC empty
    p1 <|> p2 = PC (unPC p1 <|> unPC p2)

instance MonadPlus PC where

instance Semigroup (PC val) where
    p1 <> p2 = PC (unPC p1 <> unPC p2)

instance Monoid (PC val) where
    mempty = PC mempty

instance EqProp val => EqProp (PC val) where
    p1 =-= p2 = unPC p1 =-= unPC p2

instance Arbitrary val => Arbitrary (PC val) where
    arbitrary = fmap PC arbitrary

instance Show val => Show (PC val) where
    showsPrec prec = showsPrec prec . unPC

autoPC :: Read val => NameOfPC -> PC val
autoPC expecteds = PC go where
    go :: Read val => ParserBase LocChr val
    go = PAct $ \lstr0 -> PAlt [ (PVal val1, drop (length lstr0 - length str1) lstr0) | (val1, str1) <- readsPrec 0 (map snd lstr0) ]

acceptPC :: (Char -> Bool) -> PC Char
acceptPC cond = PC go where
    go :: ParserBase LocChr Char
    go = PAct $ \lstr -> case lstr of
        ((r, c), ch) : lstr'
            | cond ch -> PAlt [(PVal ch, lstr')]
        _ -> PAlt []

consumePC :: String -> PC ()
consumePC expecteds = mapM_ acceptPC (map (==) expecteds)

matchPC :: String -> PC ()
matchPC expecteds = PC go where
    go :: ParserBase LocChr ()
    go = PAct $ \lstr0 -> if expecteds == map snd (take (length expecteds) lstr0) then PAlt [(PVal (), drop (length expecteds) lstr0)] else PAlt []

eofPC :: PC ()
eofPC = PC go where
    go :: ParserBase LocChr ()
    go = PAct $ \lstr0 -> if null lstr0 then PAlt [(PVal (), lstr0)] else PAlt []

regexPC :: RegExRep -> PC String
regexPC = PC . parserOfRegularExpression

negPC :: PC a -> PC ()
negPC = PC . negPB . unPC

runPC :: PC val -> Src -> Either ErrMsg val
runPC p str0 = case runPB (unPC p) (addLoc str0) of
    Left lstr -> Left (mkErrMsg str0 lstr)
    Right pairs -> case [ val | (val, lstr1) <- pairs, null lstr1 ] of
        [] -> Left (mkErrMsg str0 (head (sortByMerging (on (<=) length) (map snd pairs))))
        val : _ -> Right val
