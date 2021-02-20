module Z.Text.PC.Loc where

import Z.Text.Doc
import Z.Util

type Row = Int

type Col = Int

type Loc = (Row, Col)

type LocChr = (Loc, Char)

type LocStr = [LocChr]

type Src = String

type ErrMsg = String

addLoc :: Src -> LocStr
addLoc = go 1 1 where
    getNextRow :: Row -> Char -> Row
    getNextRow r '\n' = r + 1
    getNextRow r _ = r
    getNextCol :: Col -> Char -> Col
    getNextCol c '\n' = 1
    getNextCol c '\t' = c + 8
    getNextCol c _ = c + 1
    go :: Row -> Col -> String -> LocStr
    go r c [] = []
    go r c (ch : str) = ((r, c), ch) : go (getNextRow r ch) (getNextCol c ch) str

mkErrMsg :: Beauty -> Src -> LocStr -> ErrMsg
mkErrMsg beauty src lstr = renderDoc beauty err_msg where
    stuck_row :: Row
    stuck_row = case lstr of
        [] -> length (filter (\lch -> snd lch == '\n') lstr) + 1
        ((r, c), _) : _ -> r
    stuck_line :: Src
    stuck_line = splitBy '\n' src !! (stuck_row - 1)
    stuck_col :: Col
    stuck_col = case lstr of
        [] -> length stuck_line + 1
        ((r, c), _) : _ -> c
    err_msg :: Doc
    err_msg = vconcat
        [ if null lstr
            then blue (text "parsing error at EOF.")
            else blue (text "parsing error at " <> mkDoc 0 stuck_row <> text ":" <> mkDoc 0 stuck_col <> text ".")
        , hconcat
            [ vconcat
                [ text ""
                , blue (text " " <> mkDoc 0 stuck_row <> text " ")
                , text ""
                ]
            , blue mkBeam
            , vconcat
                [ text ""
                , text " " <> red (text stuck_line)
                , white stuck_col <> red (text "^")
                ]
            ]
        ]
