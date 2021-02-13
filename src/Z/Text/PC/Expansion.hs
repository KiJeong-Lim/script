module Z.Text.PC.Expansion where

import Control.Applicative
import Control.Monad
import Z.Algorithm.Sort
import Z.Text.PC
import Z.Text.PC.Base
import Z.Text.PC.Loc
import Z.Text.PC.RegEx
import Z.Text.PC.Test

acceptQuote :: PC String
acceptQuote = PC go where
    loop :: LocStr -> Either LocStr (String, LocStr)
    loop lstr0 = case map snd (take 1 lstr0) of
        [] -> Left lstr0
        ['\\'] -> case map snd (take 1 (drop 1 lstr0)) of
            ['\"'] -> do
                (quote, lstr1) <- loop (drop 2 lstr0)
                return ('\"' : quote, lstr1)
            ['\''] -> do
                (quote, lstr1) <- loop (drop 2 lstr0)
                return ('\'' : quote, lstr1)
            ['\\']  -> do
                (quote, lstr1) <- loop (drop 2 lstr0)
                return ('\\' : quote, lstr1)
            ['\n']  -> do
                (quote, lstr1) <- loop (drop 2 lstr0)
                return ('\n' : quote, lstr1)
            ['\t']  -> do
                (quote, lstr1) <- loop (drop 2 lstr0)
                return ('\t' : quote, lstr1)
            _ -> Left lstr0
        ['\n'] -> Left lstr0
        ['\t'] -> Left lstr0
        ['\"'] -> return ("", drop 1 lstr0)
        [ch] -> do
                (quote, lstr1) <- loop (drop 1 lstr0)
                return (ch : quote, lstr1)
    go :: ParserBase LocChr String
    go = PAct $ \lstr0 -> case lstr0 of
        (_, '\"') : lstr1 -> case loop lstr1 of
            Left lstr2 -> PAlt []
            Right (quote, lstr2) -> PAlt [(PVal quote, lstr2)]
        lstr1 -> PAlt []

skipWhite :: PC ()
skipWhite = PC go where
    go :: ParserBase LocChr ()
    go = PAct $ \lstr0 -> PAlt [(PVal (), dropWhile (\lch -> snd lch == ' ') lstr0)]

lend :: PC ()
lend = skipWhite *> consumePC "\n"

indent :: Int -> PC ()
indent n = consumePC space where
    space :: String
    space = replicate n ' '

smallid :: PC String
smallid = regexPC "[\'a\'-\'z\'] [\'a\'-\'z\' \'0\'-\'9\' \'_\']*"

largeid :: PC String
largeid = regexPC "[\'A\'-\'Z\'] [\'a\'-\'z\' \'0\'-\'9\' \'A\'-\'Z\']*"
