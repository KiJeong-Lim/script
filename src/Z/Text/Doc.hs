module Z.Text.Doc where

import System.Console.Pretty
import Z.Text.Doc.Internal
import Z.Text.Doc.Viewer
import Z.Util

type Doc = DOC

type Beauty = Bool

instance Semigroup DOC where
    doc1 <> doc2 = mkDH doc1 doc2

instance Monoid DOC where
    mempty = emptyDoc

isEmptyDoc :: Doc -> Bool
isEmptyDoc (DE) = True
isEmptyDoc (DT "") = True
isEmptyDoc (DH doc1 doc2) = isEmptyDoc doc1 && isEmptyDoc doc2
isEmptyDoc _ = False

emptyDoc :: Doc
emptyDoc = mkDE

mkDoc :: Show a => Precedence -> a -> Doc
mkDoc prec = mkDT . flip (showsPrec prec) ""

text :: String -> Doc
text = mkDT

textbf :: String -> Doc
textbf = mkDS Bold . mkDT

textit :: String -> Doc
textit = mkDS Italic . mkDT

hconcat :: [Doc] -> Doc
hconcat = foldr mkDH emptyDoc

vconcat :: [Doc] -> Doc
vconcat = foldr mkDH emptyDoc

mkBeam :: Doc
mkBeam = mkDB

blue :: Doc -> Doc
blue = mkDC Blue

red :: Doc -> Doc
red = mkDC Red

white :: Int -> Doc
white n = mkDT (replicate n ' ')

indentDoc :: Indentation -> [Doc] -> Doc
indentDoc n docs = vconcat (map (mkDH (white n)) docs)

listDoc :: [Doc] -> Doc
listDoc [] = text "[]"
listDoc (doc1 : docs2) = vconcat ([hconcat [text "[ ", doc1]] ++ [ hconcat [text ", ", doc2] | doc2 <- docs2 ] ++ [text "]"])

puncDoc :: Doc -> [Doc] -> [Doc]
puncDoc doc [] = []
puncDoc doc [doc1] = [doc1]
puncDoc doc (doc1 : docs2) = mkDH doc1 doc : puncDoc doc docs2

renderDoc :: Beauty -> Doc -> String
renderDoc beauty
    | beauty = renderViewer . toViewer . reduceDoc
    | otherwise = renderViewer . toViewer . reduceDoc . remove
    where
        remove :: Doc -> Doc
        remove (DE) = mkDE
        remove (DT str1) = mkDT str1
        remove (DS style1 doc1) = remove doc1
        remove (DC color1 doc1) = remove doc1
        remove (DB) = mkDB
        remove (DV doc1 doc2) = mkDV (remove doc1) (remove doc2)
        remove (DH doc1 doc2) = mkDH (remove doc1) (remove doc2)
