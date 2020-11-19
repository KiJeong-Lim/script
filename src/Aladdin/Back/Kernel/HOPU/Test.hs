module Aladdin.Back.Kernel.HOPU.Test where

import Aladdin.Back.Base.Constant
import Aladdin.Back.Base.Identifier
import Aladdin.Back.Base.Labeling
import Aladdin.Back.Base.TermNode
import Aladdin.Back.Base.TermNode.Read
import Aladdin.Back.Base.TermNode.Show
import Aladdin.Back.Base.TermNode.Util
import Aladdin.Back.Base.VarBinding
import Aladdin.Back.Kernel.Disagreement
import Aladdin.Back.Kernel.HOPU
import Aladdin.Back.Kernel.HOPU.Util
import Control.Monad
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Lib.Base

runHopuTestCase :: [Disagreement] -> Labeling -> IO ()
runHopuTestCase disagreements labeling = do
    putStrLn ("* initial-logicvar-labeling:")
    forM (Map.toList (_VarLabel labeling)) $ uncurry $ \var -> \level -> putStrLn ("  - " ++ showsPrec 0 var (" +-> " ++ showsPrec 0 level ";"))
    putStrLn ("* initial-constant-labeling:")
    forM (Map.toList (_ConLabel labeling)) $ uncurry $ \con -> \level -> putStrLn ("  - " ++ showsPrec 0 con (" +-> " ++ showsPrec 0 level ";"))
    putStrLn ("* given-disagreements = " ++ plist 2 (map (showsPrec 0) disagreements) "")
    putStrLn ("<<< Run")
    output <- runHOPU labeling disagreements
    case output of
        Nothing -> do
            putStrLn (">>> Failure")
            return ()
        Just (new_disagreements, HopuSol new_labeling subst) -> do
            putStrLn ("* final-logicvar-labeling:")
            forM (Map.toList (_VarLabel new_labeling)) $ uncurry $ \var -> \level -> putStrLn ("  - " ++ showsPrec 0 var (" +-> " ++ showsPrec 0 level ";"))
            putStrLn ("* final-constant-labeling:")
            forM (Map.toList (_ConLabel new_labeling)) $ uncurry $ \con -> \level -> putStrLn ("  - " ++ showsPrec 0 con (" +-> " ++ showsPrec 0 level ";"))
            putStrLn ("* result-substitution:")
            forM (Map.toList (unVarBinding subst)) $ uncurry $ \v -> \t -> putStrLn ("  - " ++ showsPrec 0 v (" := " ++ showsPrec 0 t "."))
            putStrLn ("* remaining-disagreements = " ++ plist 2 (map (showsPrec 0) new_disagreements) "")
            putStrLn (">>> Success")
            return ()

theSamplelabeling :: Labeling
theSamplelabeling = Labeling
    { _ConLabel = Map.fromList
        [ (DC (DC_Named (ID_Name "c0")), 0)
        , (DC (DC_Named (ID_Name "c1")), 1)
        , (DC (DC_Named (ID_Name "c2")), 2)
        , (DC (DC_Named (ID_Name "c3")), 3)
        , (DC (DC_Named (ID_Name "c4")), 4)
        , (DC (DC_Named (ID_Name "c5")), 5)
        ]
    , _VarLabel = Map.fromList
        [ (LV_Named "X0", 0)
        , (LV_Named "Y0", 0)
        , (LV_Named "X1", 1)
        , (LV_Named "Y1", 1)
        , (LV_Named "X2", 2)
        , (LV_Named "Y2", 2)
        , (LV_Named "X3", 3)
        , (LV_Named "Y3", 3)
        , (LV_Named "X4", 4)
        , (LV_Named "Y4", 4)
        , (LV_Named "X5", 5)
        , (LV_Named "Y5", 5)
        ]
    }

testHOPU :: Int -> IO ()
testHOPU 1 = runHopuTestCase disagreements theSamplelabeling where
    disagreements :: [Disagreement]
    disagreements =
        [ read "X0 c4 c1 c2 c3" :=?=: read "Y0 c5 c2 c1 c3"
        ]
testHOPU 2 = runHopuTestCase disagreements theSamplelabeling where
    disagreements :: [Disagreement]
    disagreements =
        [ read "c0 (X1 c1) (X1 c2)" :=?=: read "c0 c1 c2"
        , read "c3 (W\\ X1 c1) (X2 c2)" :=?=: read "c3 X2 (X1 c1)"
        , read "X3" :=?=: read "c3 (X4 c3) X2 (X1 c1)"
        ]
testHOPU 3 = runHopuTestCase disagreements theSamplelabeling where
    disagreements :: [Disagreement]
    disagreements =
        [ read "c0 (X1 c1) (X1 c2)" :=?=: read "c0 c1 c2"
        , read "c3 (W\\ X1 c1) (X2 c2)" :=?=: read "c3 X2 (X1 c1)"
        , read "X3" :=?=: read "c3 (X4 c5) X2 (X1 c1)"
        ]
testHOPU _ = return ()
