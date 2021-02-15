module Z.Text.PC.RegEx where

import Control.Applicative
import Control.Monad
import Data.Function
import qualified Data.List as List
import Z.Algorithm.Sort
import Z.Text.PC.Base
import Z.Text.PC.Loc
import Z.Util

type RegExRep = String

data CharSet
    = CsUniv
    | CsUnion CharSet CharSet
    | CsDiff CharSet CharSet
    | CsEnum Char Char
    | CsSingle Char
    deriving ()

data RegEx
    = ReCharSet CharSet
    | ReWord String
    | RePlus RegEx RegEx
    | ReZero
    | ReMult RegEx RegEx
    | ReStar RegEx
    deriving ()

instance Read CharSet where
    readsPrec = unPM . go where
        go :: Int -> PM CharSet
        go 0 = List.foldl' CsDiff <$> go 1 <*> many (consumeStr "\\" *> go 2)
        go 1 = List.foldl' CsUnion <$> go 2 <*> many (consumeStr " " *> go 2)
        go 2 = mconcat
            [ CsSingle <$> autoPM 0
            , CsEnum <$> autoPM 0 <* consumeStr "-" <*> autoPM 0
            , consumeStr "." *> pure CsUniv
            , go 3
            ]
        go _ = consumeStr "(" *> go 0 <* consumeStr ")"
    readList = undefined

instance Read RegEx where
    readsPrec = unPM . go where
        suffix :: PM (RegEx -> RegEx)
        suffix = mconcat
            [ consumeStr "*" *> pure (\re -> ReStar re)
            , consumeStr "+" *> pure (\re -> ReMult re (ReStar re))
            , consumeStr "?" *> pure (\re -> RePlus re (ReWord ""))
            ]
        go :: Int -> PM RegEx
        go 0 = List.foldl' RePlus <$> go 1 <*> many (consumeStr " + " *> go 1)
        go 1 = List.foldl' ReMult <$> go 2 <*> many (consumeStr " " *> go 2)
        go 2 = List.foldl' (flip ($)) <$> go 3 <*> many suffix
        go 3 = mconcat
            [ consumeStr "[" *> (ReCharSet <$> autoPM 0) <* consumeStr "]"
            , pure ReWord <* matchPrefix "\"" <*> autoPM 0
            , consumeStr "()" *> pure ReZero
            , go 4
            ]
        go _ = consumeStr "(" *> go 0 <* consumeStr ")"
    readList = undefined

parserOfRegularExpression :: RegExRep -> ParserBase LocChr String
parserOfRegularExpression regex_rep = go maybeRegEx where
    maybeRegEx :: Maybe RegEx
    maybeRegEx = case [ regex | (regex, "") <- readsPrec 0 regex_rep ] of
        [regex] -> Just regex
        _ -> Nothing
    runCharSet :: CharSet -> Char -> Bool
    runCharSet CsUniv ch = True
    runCharSet (CsUnion chs1 chs2) ch = runCharSet chs1 ch || runCharSet chs2 ch
    runCharSet (CsDiff ch1 ch2) ch = runCharSet ch1 ch && not (runCharSet ch2 ch)
    runCharSet (CsEnum ch1 ch2) ch = ch1 <= ch && ch <= ch2
    runCharSet (CsSingle ch1) ch = ch == ch1
    runRegEx :: RegEx -> LocStr -> [(String, LocStr)]
    runRegEx (ReCharSet chs) lstr0
        = case lstr0 of
            lch1 : lstr1
                | runCharSet chs (snd lch1) -> [([snd lch1], lstr1)]
            _ -> []
    runRegEx (ReWord str) lstr0
        | str == map snd (take (length str) lstr0) = [(str, drop (length str) lstr0)]
        | otherwise = []
    runRegEx (RePlus regex1 regex2) lstr0
        = runRegEx regex1 lstr0 ++ runRegEx regex2 lstr0
    runRegEx ReZero lstr0   
        = []
    runRegEx (ReMult regex1 regex2) lstr0
        = [ (str1 ++ str2, lstr2) | (str1, lstr1) <- runRegEx regex1 lstr0, (str2, lstr2) <- runRegEx regex2 lstr1 ]
    runRegEx (ReStar regex1) lstr0
        = ("", lstr0) : [ (str1 ++ str2, lstr2) | (str1, lstr1) <- runRegEx regex1 lstr0, (str2, lstr2) <- runRegEx (ReStar regex1) lstr1 ]
    go :: Maybe RegEx -> ParserBase LocChr String
    go Nothing = error ("wrong regex: " ++ show regex_rep)
    go (Just regex) = PAct $ \lstr0 -> case sortByMerging (on (>) (length . fst)) (runRegEx regex lstr0) of
        [] -> PAlt []
        (str1, lstr1) : _ -> PAlt [(PVal str1, lstr1)]
