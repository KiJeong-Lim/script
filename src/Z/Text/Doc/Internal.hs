module Z.Text.Doc.Internal where

import System.Console.Pretty
import Z.Text.Doc.Viewer
import Z.Util

data DOC
    = DE
    | DT String
    | DS Style DOC
    | DC Color DOC
    | DB
    | DV DOC DOC
    | DH DOC DOC
    deriving ()

instance Show DOC where
    show = flip (showsPrec 0) ""
    showList [] = pstr "[]"
    showList (doc : docs) = pstr "[" . go doc docs where
        go :: DOC -> [DOC] -> String -> String
        go doc1 [] = showsPrec 0 doc1 . pstr "]"
        go doc1 (doc2 : docs3) = showsPrec 0 doc1 . pstr ", " . go doc2 docs3
    showsPrec 0 doc1 = showsPrec 1 doc1
    showsPrec 1 doc1 = showsPrec 2 doc1
    showsPrec 2 doc1 = showsPrec 3 doc1
    showsPrec 3 doc1 = showsPrec 4 doc1
    showsPrec 4 doc1 = showsPrec 5 doc1
    showsPrec 5 doc1 = showsPrec 6 doc1
    showsPrec 6 doc1 = showsPrec 7 doc1
    showsPrec 7 doc1 = showsPrec 8 doc1
    showsPrec 8 doc1 = showsPrec 9 doc1
    showsPrec 9 (DT str1) = pstr "DT " . showsPrec 0 str1
    showsPrec 9 (DS style1 doc2) = pstr "DS " . showStyle style1 . pstr " " . showsPrec 10 doc2 where
        showStyle :: Style -> String -> String
        showStyle Normal = pstr "Normal"
        showStyle Bold = pstr "Bold"
        showStyle Faint = pstr "Faint"
        showStyle Italic = pstr "Italic"
        showStyle Underline = pstr "Underline"
        showStyle SlowBlink = pstr "SlowBlink"
        showStyle ColoredNormal = pstr "ColoredNormal"
        showStyle Reverse = pstr "Reverse"
    showsPrec 9 (DC color1 doc2) = pstr "DC " . showColor color1 . pstr " " . showsPrec 10 doc2 where
        showColor :: Color -> String -> String
        showColor Black = pstr "Black"
        showColor Red = pstr "Red"
        showColor Green = pstr "Green"
        showColor Yellow = pstr "Yellow"
        showColor Blue = pstr "Blue"
        showColor Magenta = pstr "Magenta"
        showColor Cyan = pstr "Cyan"
        showColor White = pstr "White"
        showColor Default = pstr "Default"
    showsPrec 9 (DV doc1 doc2) = pstr "DV " . showsPrec 10 doc1 . pstr " " . showsPrec 10 doc2
    showsPrec 9 (DH doc1 doc2) = pstr "DH " . showsPrec 10 doc1 . pstr " " . showsPrec 10 doc2
    showsPrec 10 (DE) = pstr "DE"
    showsPrec 10 (DB) = pstr "DB"
    showsPrec _ doc1 = pstr "(" . showsPrec 0 doc1 . pstr ")"

instance Semigroup DOC where
    doc1 <> doc2 = mkDH doc1 doc2

instance Monoid DOC where
    mempty = mkDE

mkDE :: DOC
mkDE = DE

mkDT :: String -> DOC
mkDT "" = DE
mkDT str1 = DT str1

mkDS :: Style -> DOC -> DOC
mkDS sty1 doc2 = doc2 `seq` DS sty1 doc2

mkDC :: Color -> DOC -> DOC
mkDC clr1 doc2 = doc2 `seq` DC clr1 doc2

mkDB :: DOC
mkDB = DB

mkDV :: DOC -> DOC -> DOC
mkDV doc1 doc2 = doc1 `seq` doc2 `seq` DV doc1 doc2

mkDH :: DOC -> DOC -> DOC
mkDH doc1 doc2 = doc1 `seq` doc2 `seq` DH doc1 doc2

toViewer :: DOC -> Viewer
toViewer (DE) = mkVE
toViewer (DT str1) = mkVT str1
toViewer (DS style1 doc2) = mkVS style1 (toViewer doc2)
toViewer (DC color1 doc2) = mkVC color1 (toViewer doc2)
toViewer (DB) = mkVB
toViewer (DV doc1 doc2) = mkVV (toViewer doc1) (toViewer doc2)
toViewer (DH doc1 doc2) = mkVH (toViewer doc1) (toViewer doc2)
