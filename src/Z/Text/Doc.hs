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
    mempty = mkDE

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
vconcat = foldr mkDV emptyDoc

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
renderDoc beauty = renderViewer beauty . toViewer . reduceDoc where
    reduceDoc :: Doc -> Doc
    reduceDoc (DE) = mkDE
    reduceDoc (DT str1) = mkDT str1
    reduceDoc (DS sty1 doc2) = if beauty then mkDS sty1 (reduceDoc doc2) else reduceDoc doc2
    reduceDoc (DC clr1 doc2) = if beauty then mkDC clr1 (reduceDoc doc2) else reduceDoc doc2
    reduceDoc (DB) = mkDB
    reduceDoc (DV doc1 doc2) = mkDV (reduceDoc doc1) (reduceDoc doc2)
    reduceDoc (DH doc1 doc2) = case (reduceDoc doc1, reduceDoc doc2) of
        (DE, doc2') -> doc2'
        (doc1', DE) -> doc1'
        (DT str1, DT str2) -> mkDT (str1 ++ str2)
        (doc1', doc2') -> mkDH doc1' doc2'
