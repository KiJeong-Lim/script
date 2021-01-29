module Z.PC.Base where

import Control.Applicative
import Control.Monad
import Z.Algorithm.Sorting

data ParserBase chr val
    = PVal
        val
    | PAlt
        [(ParserBase chr val, [chr])]
    | PAct
        ([chr] -> ParserBase chr val)
    deriving ()


instance Functor (ParserBase chr) where
    fmap a2b p1 = bindPB p1 (returnPB . a2b)

instance Applicative (ParserBase chr) where
    pure = returnPB
    p1 <*> p2 = bindPB p1 (flip fmap p2)

instance Monad (ParserBase chr) where
    p1 >>= p2 = bindPB p1 p2

instance Alternative (ParserBase chr) where
    empty = emptyPB
    p1 <|> p2 = appendPB p1 p2

instance MonadPlus (ParserBase chr) where

instance Semigroup (ParserBase chr val) where
    (<>) = (<|>)

instance Monoid (ParserBase chr val) where
    mempty = empty

instance (Show chr, Show val) => Show (ParserBase chr val) where
    show = flip (showsPrec 0) ""
    showList [] str = "[]" ++ str
    showList (x : xs) str = "[" ++ go x xs str where
        go :: (Show chr, Show val) => ParserBase chr val -> [ParserBase chr val] -> String -> String
        go p1 [] str = showsPrec 0 p1 ("]" ++ str)
        go p1 (p2 : ps) str = showsPrec 0 p1 ("," ++ go p2 ps str)
    showsPrec prec = go where
        parenthesize :: Int -> (String -> String) -> String -> String
        parenthesize prec' strstr str
            | prec > prec' = "(" ++ strstr (")" ++ str)
            | otherwise = strstr str
        go :: (Show chr, Show val) => ParserBase chr val -> String -> String
        go (PVal val1) = parenthesize 9 (\str -> "PVal " ++ showsPrec 10 val1 str)
        go (PAlt alts1) = parenthesize 9 (\str -> "PAct " ++ showList alts1 str)
        go (PAct act1) = parenthesize 9 (\str -> "PAct ([] +-> " ++ showsPrec 0 (act1 []) (")" ++ str))

unPB :: ParserBase chr val -> [chr] -> [(ParserBase chr val, [chr])]
unPB (PVal val1) str0 = [(PVal val1, str0)]
unPB (PAlt alts1) str0 = alts1
unPB (PAct act1) str0 = unPB (act1 str0) str0

returnPB :: val -> ParserBase chr val
returnPB val1 = PVal val1

bindPB :: ParserBase chr val1 -> (val1 -> ParserBase chr val2) -> ParserBase chr val2
bindPB (PVal val1) p2 = p2 val1
bindPB (PAlt alts1) p2 = PAlt [ (bindPB p1 p2, str1) | (p1, str1) <- alts1 ]
bindPB (PAct act1) p2 = PAct $ \str0 -> bindPB (act1 str0) p2

emptyPB :: ParserBase chr val
emptyPB = PAlt []

appendPB :: ParserBase chr val -> ParserBase chr val -> ParserBase chr val
appendPB = go where
    go :: ParserBase chr val -> ParserBase chr val -> ParserBase chr val
    go p1 p2 = PAct $ \str0 -> PAlt (unPB p1 str0 ++ unPB p2 str0)

mkPB :: ([chr] -> [(val, [chr])]) -> ParserBase chr val
mkPB _ReadS = PAct $ \str0 -> PAlt [ (PVal val1, str1) | (val1, str1) <- _ReadS str0 ]

negPB :: ParserBase chr val -> ParserBase chr ()
negPB p1 = PAct $ \str0 -> case unPB p1 str0 of
    [] -> PAlt [(PVal (), str0)]
    alts1 -> PAlt []

runPB :: ParserBase chr val -> [chr] -> Either [chr] [(val, [chr])]
runPB = go where
    findShortest :: [[chr]] -> [chr]
    findShortest = head . sortByMerging (\x1 -> \x2 -> length x1 <= length x2)
    go :: ParserBase chr val -> [chr] -> Either [chr] [(val, [chr])]
    go (PVal val1) str0 = Right [(val1, str0)]
    go (PAlt alts1) str0
        = case [ go p1 str1 | (p1, str1) <- alts1 ] of
            [] -> Left str0
            results -> case [ (val2, str2) | Right pairs <- results, (val2, str2) <- pairs ] of
                [] -> Left (findShortest [ str2 | Left str2 <- results ])
                pairs -> Right pairs
    go (PAct act1) str0 = go (act1 str0) str0
