module LGS.Make where

import Debug.Trace
import Control.Monad
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.State.Strict
import Control.Monad.Trans.Writer.Strict
import Data.Functor.Identity
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import LGS.Util

theCsUniv :: Set.Set Char
theCsUniv = Set.fromList (['a' .. 'z'] ++ ['A' .. 'Z'] ++ " `~0123456789!@#$%^&*()-=_+[]\\{}|;\':\"\n,./<>?")

getCharSet :: CharSet -> Set.Set Char
getCharSet = go where
    go :: CharSet -> Set.Set Char
    go (CsSingle ch) = Set.singleton ch
    go (CsEnum ch1 ch2) = Set.fromAscList [ch1 .. ch2]
    go (chs1 `CsUnion` chs2) = go chs1 `Set.union` go chs2
    go (chs1 `CsDiff` chs2) = go chs1 `Set.difference` go chs2
    go CsUniv = theCsUniv

mkstrict :: (a, b) -> (a, b)
mkstrict pair = snd pair `seq` pair

getUnitedNFAfromREs :: [(RegEx, Maybe RegEx)] -> NFA
getUnitedNFAfromREs regexes = runIdentity go where
    getNewQ :: StateT (ParserS, Map.Map (ParserS, Maybe Char) (Set.Set ParserS)) Identity ParserS
    getNewQ = do
        (maximumOfQs, deltas) <- get
        put (maximumOfQs + 1, deltas)
        return maximumOfQs
    drawTransition :: ((ParserS, Maybe Char), ParserS) -> StateT (ParserS, Map.Map (ParserS, Maybe Char) (Set.Set ParserS)) Identity ()
    drawTransition (key, q) = do
        (maximumOfQs, deltas) <- get
        case Map.lookup key deltas of
            Nothing -> put (maximumOfQs, Map.insert key (Set.singleton q) deltas)
            Just qs -> put (maximumOfQs, Map.update (const (Just (Set.insert q qs))) key deltas)
    loop :: RegEx -> StateT (ParserS, Map.Map (ParserS, Maybe Char) (Set.Set ParserS)) Identity (ParserS, ParserS)
    loop (ReUnion regex1 regex2) = do
        (qi1, qf1) <- loop regex1
        (qi2, qf2) <- loop regex2
        qi <- getNewQ
        qf <- getNewQ
        drawTransition ((qi, Nothing), qi1)
        drawTransition ((qi, Nothing), qi2)
        drawTransition ((qf1, Nothing), qf)
        drawTransition ((qf2, Nothing), qf)
        return (qi, qf)
    loop (ReConcat regex1 regex2) = do
        (qi1, qf1) <- loop regex1
        (qi2, qf2) <- loop regex2
        drawTransition ((qf1, Nothing), qi2)
        return (qi1, qf2)
    loop (ReStar regex1) = do
        (qi1, qf1) <- loop regex1
        qi <- getNewQ
        qf <- getNewQ
        drawTransition ((qi, Nothing), qi1)
        drawTransition ((qf1, Nothing), qi1)
        drawTransition ((qf1, Nothing), qf)
        drawTransition ((qi, Nothing), qf)
        return (qi, qf)
    loop ReZero = do
        qi <- getNewQ
        qf <- getNewQ
        return (qi, qf)
    loop (ReWord str) = do
        let n = length str
        qs <- mapM (\_ -> getNewQ) [0, 1 .. n]
        mapM drawTransition (zip (zip (take n qs) (map Just str)) (drop 1 qs))
        return (qs !! 0, qs !! n)
    loop (ReCharSet chs) = do
        qi <- getNewQ
        qf <- getNewQ
        mapM drawTransition (zip (zip (repeat qi) (map Just (Set.toList (getCharSet chs)))) (repeat qf))
        return (qi, qf)
    loop (ReDagger regex1) = do
        (qi1, qf1) <- loop regex1
        qi <- getNewQ
        qf <- getNewQ
        drawTransition ((qi, Nothing), qi1)
        drawTransition ((qf1, Nothing), qi1)
        drawTransition ((qf1, Nothing), qf)
        return (qi, qf)
    loop (ReQuest regex1) = do
        (qi1, qf1) <- loop regex1
        qi <- getNewQ
        qf <- getNewQ
        drawTransition ((qi, Nothing), qi1)
        drawTransition ((qf1, Nothing), qf)
        drawTransition ((qi, Nothing), qf)
        return (qi, qf)
    go :: Identity NFA
    go = do
        let n = length regexes
        (markeds, (numberOfQs, deltas)) <- flip runStateT (n + 1, Map.empty) $ fmap (Map.fromAscList . concat) $ sequence
            [ case regexes !! (i - 1) of
                (regex, Nothing) -> do
                    (qi, qf) <- loop regex
                    drawTransition ((0, Nothing), qi)
                    drawTransition ((qf, Nothing), i)
                    return []
                (regex1, Just regex2) -> do
                    (qi1, qf1) <- loop regex1
                    (qi2, qf2) <- loop regex2
                    q <- getNewQ
                    drawTransition ((0, Nothing), qi1)
                    drawTransition ((qf1, Nothing), q)
                    drawTransition ((q, Nothing), qi2)
                    drawTransition ((qf2, Nothing), i)
                    return [(i, q)]
            | i <- [1, 2 .. n]
            ]
        return $ NFA 
            { getInitialQOfNFA = 0
            , getFinalQsOfNFA = Set.fromAscList [1, 2 .. n]
            , getTransitionsOfNFA = deltas
            , getMarkedQsOfNFA = markeds
            }

makeDFAfromNFA :: NFA -> DFA
makeDFAfromNFA (NFA q0 qfs deltas markeds) = runIdentity go where
    eClosure :: Set.Set ParserS -> Set.Set ParserS
    eClosure qs = if qs == qs' then qs' else eClosure qs' where
        qs' :: Set.Set ParserS
        qs' = foldr Set.union qs
            [ case Map.lookup (q, Nothing) deltas of
                Nothing -> Set.empty
                Just ps -> ps
            | q <- Set.toList qs
            ]
    getNexts :: Set.Set ParserS -> Char -> Set.Set ParserS
    getNexts qs ch = Set.unions
        [ case Map.lookup (q, Just ch) deltas of
            Nothing -> Set.empty
            Just ps -> ps
        | q <- Set.toList qs
        ]
    drawGraph :: Map.Map (Set.Set ParserS) ParserS -> [((Set.Set ParserS, ParserS), Char)] -> StateT (Map.Map (ParserS, Char) ParserS) Identity (Map.Map (Set.Set ParserS) ParserS)
    drawGraph mapOldToNew [] = return mapOldToNew
    drawGraph mapOldToNew (((qs, q'), ch) : triples) = do
        let ps = eClosure (getNexts qs ch)
        deltas' <- get
        case Map.lookup ps mapOldToNew of
            Nothing -> do
                let p' = Map.size mapOldToNew
                put (Map.insert (q', ch) p' deltas')
                drawGraph (Map.insert ps p' mapOldToNew) triples
            Just p' -> do
                put (Map.insert (q', ch) p' deltas')
                drawGraph mapOldToNew triples
    loop :: Map.Map (Set.Set ParserS) ParserS -> StateT (Map.Map (ParserS, Char) ParserS) Identity (Map.Map ParserS ParserS, Map.Map ParserS (Set.Set ParserS))
    loop mapOldToNew = do
        mapOldToNew' <- drawGraph mapOldToNew ((,) <$> Map.toList mapOldToNew <*> Set.toList theCsUniv)
        if mapOldToNew == mapOldToNew'
            then return
                ( Map.fromList
                    [ (q', qf)
                    | qf <- Set.toDescList qfs
                    , (qs, q') <- Map.toList mapOldToNew'
                    , qf `Set.member` qs
                    ]
                , Map.fromAscList
                    [ mkstrict
                        ( i
                        , Set.fromList
                            [ q' 
                            | (qs, q') <- Map.toList mapOldToNew'
                            , q `Set.member` qs
                            ]
                        )
                    | (i, q) <- Map.toAscList markeds
                    ]
                )
            else loop mapOldToNew'
    go :: Identity DFA
    go = do
        let q0' = 0
        ((qfs', markeds'), deltas') <- runStateT (loop (Map.singleton (eClosure (Set.singleton q0)) q0')) Map.empty
        return (DFA q0' qfs' deltas' markeds')

makeMinimalDFA :: DFA -> DFA
makeMinimalDFA (DFA q0 qfs deltas markeds) = result where
    reachables :: Set.Set ParserS
    reachables = go (Set.singleton q0) where
        go :: Set.Set ParserS -> Set.Set ParserS
        go qs = if qs == qs' then qs' else go qs' where
            qs' :: Set.Set ParserS
            qs' = foldr Set.insert qs
                [ p
                | ((q, _), p) <- Map.toList deltas
                , q `Set.member` qs
                ]
    distinguishedPairs :: Set.Set (ParserS, ParserS)
    distinguishedPairs = go initialPairs where
        initialPairs :: Set.Set (ParserS, ParserS)
        initialPairs = Set.fromAscList
            [ (q, q')
            | q <- Set.toAscList reachables
            , q' <- Set.toAscList reachables
            , Map.lookup q qfs /= Map.lookup q' qfs
            ]
        go :: Set.Set (ParserS, ParserS) -> Set.Set (ParserS, ParserS)
        go pairs = if pairs == pairs' then pairs' else go pairs' where
            pairs' :: Set.Set (ParserS, ParserS)
            pairs' = foldr Set.union pairs
                [ Set.fromAscList
                    [ (q, q')
                    | q <- Set.toAscList reachables
                    , q' <- Set.toAscList reachables
                    , (deltas Map.! (q, ch), deltas Map.! (q', ch)) `Set.member` pairs
                    ]
                | ch <- Set.toList theCsUniv
                ]
    winners :: Set.Set ParserS
    winners = go q0 (Set.toList reachables) where
        go :: ParserS -> [ParserS] -> Set.Set ParserS
        go p qs = case [ q | q <- qs, (p, q) `Set.member` distinguishedPairs ] of
            [] -> Set.singleton p
            p' : qs' -> Set.insert p (go p' qs')
    result :: DFA
    result = DFA
        { getInitialQOfDFA = q0
        , getFinalQsOfDFA = Map.fromAscList
            [ (qf, label)
            | (qf, label) <- Map.toAscList qfs
            , qf `Set.member` winners
            ]
        , getTransitionsOfDFA = Map.fromAscList
            [ mkstrict
                ( (q, ch)
                , head
                    [ q'
                    | q' <- Set.toList winners
                    , not ((q', p) `Set.member` distinguishedPairs)
                    ]
                )
            | ((q, ch), p) <- Map.toAscList deltas
            , q `Set.member` winners
            ]
        , getMarkedQsOfDFA = Map.map (Set.filter (\q -> q `Set.member` winners)) markeds
        }

deleteDeadStates :: DFA -> DFA
deleteDeadStates (DFA q0 qfs deltas markeds) = runIdentity go where
    edges :: Set.Set (ParserS, ParserS)
    edges = Set.fromList [ (p, q) | ((q, ch), p) <- Map.toList deltas ]
    loop :: [ParserS] -> StateT (Set.Set ParserS) Identity ()
    loop ps = do
        forM ps $ \p -> do
            visiteds <- get
            when (not (p `Set.member` visiteds)) $ do
                modify (Set.insert p)
                loop [ q' | (p', q') <- Set.toList edges, p == p' ]
        return ()
    go :: Identity DFA
    go = do
        (_, winners) <- runStateT (loop (Set.toList (Map.keysSet qfs))) Set.empty
        return $ DFA
            { getInitialQOfDFA = q0
            , getFinalQsOfDFA = qfs
            , getTransitionsOfDFA = Map.fromAscList
                [ ((q, ch), p)
                | ((q, ch), p) <- Map.toAscList deltas
                , q `Set.member` winners
                , p `Set.member` winners
                ]
            , getMarkedQsOfDFA = Map.map (Set.filter (\q -> q `Set.member` winners)) markeds
            }

makeDFAfromREs :: [(RegEx, Maybe RegEx)] -> DFA
makeDFAfromREs = deleteDeadStates . makeMinimalDFA . makeDFAfromNFA . getUnitedNFAfromREs

reduceRegEx :: RegEx -> RegEx
reduceRegEx (ReConcat re1 re2) = case (reduceRegEx re1, reduceRegEx re2) of
    (ReWord str1, ReWord str2) -> mkReWord (str1 ++ str2)
    (ReZero, re3) -> mkReZero
    (re3, ReZero) -> mkReZero
    (ReUnion re3 re4, re5) -> mkReUnion (reduceRegEx (mkReConcat re3 re5)) (reduceRegEx (mkReConcat re4 re5))
    (re3, ReUnion re4 re5) -> mkReUnion (reduceRegEx (mkReConcat re3 re4)) (reduceRegEx (mkReConcat re3 re5))
    (ReWord [], re3) -> re3
    (re3, ReWord []) -> re3
    (re3, re4) -> mkReConcat re3 re4
reduceRegEx (ReUnion re1 re2) = case (reduceRegEx re1, reduceRegEx re2) of
    (ReCharSet chs1, ReCharSet chs2) -> ReCharSet (CsUnion chs1 chs2)
    (ReZero, re3) -> re3
    (re3, ReZero) -> re3
    (ReStar re3, ReStar re4) -> if re3 == re4 then mkReStar re3 else mkReUnion (mkReStar re3) (mkReStar re4)
    (ReStar re3, re4) -> if re3 == re4 then mkReStar re3 else mkReUnion (mkReStar re3) re4
    (re3, ReStar re4) -> if re3 == re4 then mkReStar re4 else mkReUnion re3 (mkReStar re4)
    (re3, re4) -> if re3 == re4 then re3 else mkReUnion re3 re4
reduceRegEx (ReStar re1) = case reduceRegEx re1 of
    ReZero -> mkReWord []
    ReWord [] -> mkReWord []
    ReStar re2 -> mkReStar re2
    re2 -> mkReStar re2
reduceRegEx re = re

makeJumpRegexTable :: DFA -> Map.Map (ParserS, ParserS) RegEx
makeJumpRegexTable (DFA q0 qfs delta markeds) = makeClosure (length qs) where
    qs :: [ParserS]
    qs = Set.toAscList theSetOfAllStatesInGraph where
        theSetOfAllStatesInGraph :: Set.Set ParserS
        theSetOfAllStatesInGraph = Set.unions
            [ Set.singleton q0
            , Map.keysSet qfs
            , Set.unions [ Set.fromList [q, p] | ((q, ch), p) <- Map.toAscList delta ]
            ]
    makeRegExFromCharSet :: (Char -> Bool) -> RegEx
    makeRegExFromCharSet cond
        = case List.partition cond (Set.toDescList theCsUniv) of
            (yess, nos)
                | length nos < 5 -> mkReCharSet (List.foldl' mkCsDiff mkCsUniv (map mkCsSingle nos))
                | otherwise -> foldr mkReUnion mkReZero
                    [ case pair of
                        (ch1, ch2) -> if ch1 == ch2 then mkReWord [ch1] else mkReCharSet (mkCsEnum ch1 ch2)
                    | pair <- foldr loop [] yess
                    ]
        where
            loop :: Char -> [(Char, Char)] -> [(Char, Char)]
            loop ch0 pairs0 = case List.partition (\pair -> snd pair == pred ch0) pairs0 of
                ([], pairs1) -> (ch0, ch0) : pairs1
                ([(ch1, ch2)], pairs1) -> (ch1, ch0) : pairs1
    lookTable :: Map.Map (ParserS, ParserS) RegEx -> (ParserS, ParserS) -> RegEx
    lookTable table = maybe ReZero id . flip Map.lookup table
    makeClosure :: Int -> Map.Map (ParserS, ParserS) RegEx
    makeClosure n
        | n < 0 = undefined
        | n == 0 = init
        | n > 0 = loop (qs !! (n - 1)) (makeClosure (n - 1))
        where
            init :: Map.Map (ParserS, ParserS) RegEx
            init = fromMaybeList
                [ case reduceRegEx (mkReUnion (if q1 == q2 then mkReWord [] else mkReZero) (makeRegExFromCharSet (\ch -> Map.lookup (q1, ch) delta == Just q2))) of
                    ReZero -> ((q1, q2), Nothing)
                    re -> ((q1, q2), Just re)
                | q1 <- qs
                , q2 <- qs
                ]
            loop :: ParserS -> Map.Map (ParserS, ParserS) RegEx -> Map.Map (ParserS, ParserS) RegEx
            loop q prev = fromMaybeList
                [ case reduceRegEx (mkReUnion (prev `lookTable` (q1, q2)) (mkReConcat (prev `lookTable` (q1, q)) (mkReConcat (mkReStar (prev `lookTable` (q, q))) (prev `lookTable` (q, q2))))) of
                    ReZero -> ((q1, q2), Nothing)
                    re -> ((q1, q2), Just re)
                | q1 <- qs
                , q2 <- qs
                ]
            fromMaybeList :: Ord k => [(k, Maybe a)] -> Map.Map k a
            fromMaybeList pairs = Map.fromList [ mkstrict (k, a) | (k, Just a) <- pairs ]

generateRegexTable :: DFA -> Map.Map ParserS RegEx
generateRegexTable dfa = result where
    qs :: [ParserS]
    qs = Set.toAscList theSetOfAllStatesInGraph where
        theSetOfAllStatesInGraph :: Set.Set ParserS
        theSetOfAllStatesInGraph = Set.unions
            [ Set.singleton (getInitialQOfDFA dfa)
            , Map.keysSet (getFinalQsOfDFA dfa)
            , Set.unions [ Set.fromList [q, p] | ((q, ch), p) <- Map.toAscList (getTransitionsOfDFA dfa) ]
            ]
    theJumpTable :: Map.Map (ParserS, ParserS) RegEx
    theJumpTable = makeJumpRegexTable dfa
    result :: Map.Map ParserS RegEx
    result = Map.fromAscList
        [ mkstrict
            ( q
            , theJumpTable Map.! (getInitialQOfDFA dfa, q)
            )
        | q <- qs
        ]
