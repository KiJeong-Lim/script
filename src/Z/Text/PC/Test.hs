module Z.Text.PC.Test where

import Test.QuickCheck
import Test.QuickCheck.Checkers
import Test.QuickCheck.Classes
import Z.Text.PC.Base

instance (CoArbitrary chr, Arbitrary chr, Arbitrary val) => Arbitrary (ParserBase chr val) where
    arbitrary = choose (1, 5) >>= loop where
        loop :: (CoArbitrary chr, Arbitrary chr, Arbitrary val) => Int -> Gen (ParserBase chr val)
        loop rank
            | rank <= 0 = do
                val1 <- arbitrary
                return (PVal val1)
            | otherwise = oneof
                [ do
                    act1 <- liftArbitrary (loop (rank - 1))
                    return (PAct act1)
                , do
                    sz <- choose (1, 5)
                    alts1 <- vectorOf sz $ do
                        p <- loop (rank - 1)
                        str <- arbitrary
                        return (p, str)
                    return (PAlt alts1)
                ]

instance (Show chr, Arbitrary chr, EqProp val, EqProp chr) => EqProp (ParserBase chr val) where
    parser1 =-= parser2 = runPB parser1 =-= runPB parser2

checkParserBaseIsMonad :: TestBatch
checkParserBaseIsMonad = go undefined where
    go :: ParserBase Char (Int, Int, Int) -> TestBatch
    go = monad

checkParserBaseIsMonadPlus :: TestBatch
checkParserBaseIsMonadPlus = go undefined where
    go :: ParserBase Char (Int, Int) -> TestBatch
    go = monadPlus

testParserBase :: IO ()
testParserBase = do
    quickBatch checkParserBaseIsMonad
    quickBatch checkParserBaseIsMonadPlus
    return ()
