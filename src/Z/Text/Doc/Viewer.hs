module Z.Text.Doc.Viewer where

import System.Console.Pretty

data Viewer
    = VEmpty
    | VText String
    | VStyle Style Viewer
    | VColor Color Viewer
    | VBeam
    | VVertical Viewer Viewer
    | VHorizontal Viewer Viewer
    | VField Int Int [String]
    deriving ()

mkVE :: Viewer
mkVE = VEmpty

mkVT :: String -> Viewer
mkVT ss1 = ss1 `seq` VText ss1

mkVS :: Style -> Viewer -> Viewer
mkVS s1 v2 = v2 `seq` VStyle s1 v2

mkVC :: Color -> Viewer -> Viewer
mkVC c1 v2 = v2 `seq` VColor c1 v2

mkVB :: Viewer
mkVB = VBeam

mkVV :: Viewer -> Viewer -> Viewer
mkVV v1 v2 = v1 `seq` v2 `seq` VVertical v1 v2

mkVH :: Viewer -> Viewer -> Viewer
mkVH v1 v2 = v1 `seq` v2 `seq` VHorizontal v1 v2

mkVF :: Int -> Int -> [String] -> Viewer
mkVF row1 col1 field1 = row1 `seq` col1 `seq` field1 `seq` VField row1 col1 field1

one :: a -> [a]
one a = a `seq` [a]

renderViewer :: Bool -> Viewer -> String
renderViewer beauty = unlines . linesFromVField . normalizeV where
    elimPretty :: Viewer -> Viewer
    elimPretty (VColor c1 v2) = elimPretty v2
    elimPretty (VStyle s1 v2) = elimPretty v2
    elimPretty v = v
    getMaxHeight :: [Viewer] -> Int
    getMaxHeight vs = foldr max 0 [ col | VField row col field <- map elimPretty vs ]
    getMaxWidth :: [Viewer] -> Int
    getMaxWidth vs = foldr max 0 [ row | VField row col field <- map elimPretty vs ]
    expandHeight :: Int -> Viewer -> Viewer
    expandHeight col (VBeam) = mkVF 1 col (replicate col "|")
    expandHeight col (VEmpty) = mkVF 0 col (replicate col "")
    expandHeight col (VStyle s1 v2) = mkVS s1 (expandHeight col v2)
    expandHeight col (VColor c1 v2) = mkVC c1 (expandHeight col v2)
    expandHeight col (VField row col' field) = mkVF row col (field ++ replicate (col - col') (replicate row ' '))
    expandWidth :: Int -> Viewer -> Viewer
    expandWidth row (VBeam) = if beauty then mkVS Bold (mkVF row 1 [replicate row '-']) else mkVF row 1 [replicate row '-']
    expandWidth row (VEmpty) = mkVF row 0 []
    expandWidth row (VStyle s1 v2) = mkVS s1 (expandWidth row v2)
    expandWidth row (VColor c1 v2) = mkVC c1 (expandWidth row v2)
    expandWidth row (VField row' col field) = mkVF row col [ str ++ replicate (row - row') ' ' | str <- field ]
    horizontal :: Viewer -> [Viewer]
    horizontal (VBeam) = one mkVB
    horizontal (VEmpty) = one mkVE
    horizontal (VField row col field) = one (mkVF row col field)
    horizontal (VColor c1 v2) = map (mkVC c1) (horizontal v2)
    horizontal (VStyle s1 v2) = map (mkVS s1) (horizontal v2)
    horizontal (VText ss1) = one (mkVF (length ss1) 1 [ss1])
    horizontal (VVertical v1 v2) = one (normalizeV (mkVV v1 v2))
    horizontal (VHorizontal v1 v2) = horizontal v1 ++ horizontal v2
    vertical :: Viewer -> [Viewer]
    vertical (VBeam) = one mkVB
    vertical (VEmpty) = one mkVE
    vertical (VField row col field) = one (mkVF row col field)
    vertical (VColor c1 v2) = map (mkVC c1) (vertical v2)
    vertical (VStyle s1 v2) = map (mkVS s1) (vertical v2)
    vertical (VText ss1) = one (mkVF (length ss1) 1 [ss1])
    vertical (VHorizontal v1 v2) = one (normalizeH (mkVH v1 v2))
    vertical (VVertical v1 v2) = vertical v1 ++ vertical v2
    makePretty :: Viewer -> Viewer
    makePretty (VColor c1 v2) = case makePretty v2 of
        VField row2 col2 field2 -> mkVF row2 col2 (map (color c1) field2)
    makePretty (VStyle s1 v2) = case makePretty v2 of
        VField row2 col2 field2 -> mkVF row2 col2 (map (style s1) field2)
    makePretty (VField row1 col1 field1) = mkVF row1 col1 field1
    hsum :: Int -> [Viewer] -> Viewer
    hsum col [] = mkVF 0 col (replicate col "")
    hsum col (v : vs) = case (makePretty v, hsum col vs) of
        (VField row1 _ field1, VField row2 _ field2) -> mkVF (row1 + row2) col (zipWith (++) field1 field2)
    vsum :: Int -> [Viewer] -> Viewer
    vsum row [] = mkVF row 0 []
    vsum row (v : vs) = case (makePretty v, vsum row vs) of
        (VField _ col1 field1, VField _ col2 field2) -> mkVF row (col1 + col2) (field1 ++ field2)
    normalizeH :: Viewer -> Viewer
    normalizeH = merge . concat . map horizontal . flatten where
        flatten :: Viewer -> [Viewer]
        flatten (VHorizontal v1 v2) = flatten v1 ++ flatten v2
        flatten v1 = one v1
        merge :: [Viewer] -> Viewer
        merge vs = hsum (getMaxHeight vs) (map (expandHeight (getMaxHeight vs)) vs)
    normalizeV :: Viewer -> Viewer
    normalizeV = merge . concat . map vertical . flatten where
        flatten :: Viewer -> [Viewer]
        flatten (VVertical v1 v2) = flatten v1 ++ flatten v2
        flatten v1 = one v1
        merge :: [Viewer] -> Viewer
        merge vs = vsum (getMaxWidth vs) (map (expandWidth (getMaxWidth vs)) vs)
    linesFromVField :: Viewer -> [String]
    linesFromVField (VField row1 col1 field1) = field1
