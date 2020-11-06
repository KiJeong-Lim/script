module Aladdin.BackEnd.Kernel.KernelTest where

import Aladdin.BackEnd.Back
import Aladdin.BackEnd.Kernel.HOPU
import Aladdin.BackEnd.Kernel.Runtime
import Control.Monad
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Unique
import Lib.Base
import Test.QuickCheck

instance Arbitrary VI where
    arbitrary = do
        n <- genNat
        return (VI_Named ("V_" ++ show n))
    shrink = shrinkNothing

instance Arbitrary CI where
    arbitrary = do
        n <- genNat
        return (CI_Named ("c_" ++ show n))
    shrink = shrinkNothing

instance Arbitrary id => Arbitrary (Atom id) where
    arbitrary = do
        id1 <- arbitrary
        return (mkTermAtom id1)
    shrink (Atom { isType = isty, _ID = id1 }) = [ Atom { isType = isty, _ID = id1' } | id1' <- shrink id1 ]

instance Arbitrary TermNode where
    arbitrary = go (vectorOf 10 genNCon) (vectorOf 10 genLVar) where
        go :: Gen [TermNode] -> Gen [TermNode] -> Gen TermNode
        go gen_cs gen_vs = do
            cs <- gen_cs
            vs <- gen_vs
            let genTerm rank = genTerm_aux rank 0
                genTerm_aux 0 lambda = elements (cs ++ vs ++ map mkNIdx [1, 2 .. lambda])
                genTerm_aux rank lambda = oneof
                    [ do
                        t1 <- genTerm_aux (rank - 1) lambda
                        t2 <- genTerm_aux (rank - 1) lambda
                        return (mkNApp t1 t2)
                    , do
                        t <- genTerm_aux (rank - 1) (lambda + 1)
                        return (mkNAbs t)
                    ]
            rank1 <- genNat
            genTerm rank1
    shrink (LVar v) = []
    shrink (NCon c) = []
    shrink (NIdx i) = []
    shrink (NApp t1 t2) = [t1, t2] ++ [ NApp t1' t2' | (t1', t2') <- shrink (t1, t2) ]
    shrink (NAbs t) = [t] ++ [ NAbs t' | t' <- shrink t ]
    shrink (Susp t ol nl env) = shrink (rewriteWithSusp t ol nl env NF)

instance Arbitrary Disagreement where
    arbitrary = go (vectorOf 10 genNCon) (vectorOf 10 genLVar) where
        go :: Gen [TermNode] -> Gen [TermNode] -> Gen Disagreement
        go gen_cs gen_vs = do
            cs <- gen_cs
            vs <- gen_vs
            let genTerm rank = genTerm_aux rank 0
                genTerm_aux 0 lambda = elements (cs ++ vs ++ map mkNIdx [1, 2 .. lambda])
                genTerm_aux rank lambda = oneof
                    [ do
                        t1 <- genTerm_aux (rank - 1) lambda
                        t2 <- genTerm_aux (rank - 1) lambda
                        return (mkNApp t1 t2)
                    , do
                        t <- genTerm_aux (rank - 1) (lambda + 1)
                        return (mkNAbs t)
                    ]
            rank1 <- genNat
            rank2 <- genNat
            lhs <- genTerm rank1
            rhs <- genTerm rank2
            return (Disagreement lhs rhs)
    shrink (Disagreement lhs rhs) = [ Disagreement lhs' rhs' | (lhs', rhs') <- shrink (lhs, rhs) ]

genNat :: Gen Int
genNat = arbitrary `suchThat` (\n -> n >= 0)

genNCon :: Gen TermNode
genNCon = do
    con <- arbitrary
    return (mkNCon con)

genLVar :: Gen TermNode
genLVar = do
    var <- arbitrary
    return (mkLVar var)

hoputest :: [Disagreement] -> Labeling -> IO ()
hoputest disagreements labeling = do
    output <- runHOPU disagreements labeling
    case output of
        Nothing -> putStrLn ">>> failure!"
        Just (HopuEnv labeling' binding', disagreements') -> do
            putStrLn ">>> success!"
            putStrLn "* var-labeling:"
            forM (Map.toList (_VarLabel labeling')) $ uncurry $ \var -> \label -> putStrLn ("    " ++ show var ++ " +-> " ++ show label)
            putStrLn "* con-labeling:"
            forM (Map.toList (_ConLabel labeling')) $ uncurry $ \con -> \label -> putStrLn ("    " ++ show con ++ " +-> " ++ show label)
            putStrLn "* binding:"
            forM (Map.toList (getVarBinding binding')) $ uncurry $ \v -> \t -> putStrLn ("    " ++ show v ++ " +-> " ++ show t)
            putStrLn "* disagreements:"
            forM disagreements' $ \eqn -> putStrLn ("    " ++ show eqn)
            return ()

test :: Int -> IO ()
test 1 = hoputest disagreements labeling where
    disagreements :: [Disagreement]
    disagreements = [Disagreement (read "X c4 c1 c2 c3") (read "Y c5 c2 c1 c3")]
    labeling :: Labeling
    labeling = Labeling
        { _ConLabel = Map.fromList
            [ (mkTermAtom (CI_Named "c1"), 1)
            , (mkTermAtom (CI_Named "c2"), 2)
            , (mkTermAtom (CI_Named "c3"), 3)
            , (mkTermAtom (CI_Named "c4"), 4)
            , (mkTermAtom (CI_Named "c5"), 5)
            ]
        , _VarLabel = Map.fromList
            [ (mkTermAtom (VI_Named "X"), 0)
            , (mkTermAtom (VI_Named "Y"), 0)
            ]
        }
test 2 = hoputest disagreements labeling where
    disagreements :: [Disagreement]
    disagreements = [Disagreement (read "X c4 c1 c2 c3") (read "X c5 c2 c1 c3")]
    labeling :: Labeling
    labeling = Labeling
        { _ConLabel = Map.fromList
            [ (mkTermAtom (CI_Named "c1"), 1)
            , (mkTermAtom (CI_Named "c2"), 2)
            , (mkTermAtom (CI_Named "c3"), 3)
            , (mkTermAtom (CI_Named "c4"), 4)
            , (mkTermAtom (CI_Named "c5"), 5)
            ]
        , _VarLabel = Map.fromList
            [ (mkTermAtom (VI_Named "X"), 0)
            , (mkTermAtom (VI_Named "Y"), 0)
            ]
        }
test _ = return ()
