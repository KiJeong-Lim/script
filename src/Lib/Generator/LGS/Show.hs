module Lib.Generator.LGS.Show where

import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.State.Strict
import Control.Monad.Trans.Writer.Strict
import Data.Functor.Identity
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Lib.Base
import Lib.Generator.LGS.Util

instance Show NFA where
    showsPrec _ (NFA q0 qfs deltas markeds) = strcat
        [ strstr "NFA" . nl
        , strstr "    { getInitialQOfNFA = " . showsPrec 0 q0 . nl
        , strstr "    , getFinalQsOfNFA = XSet.fromAscList [" . ppunc ", " (map (showsPrec 0) (Set.toAscList qfs)) . strstr "]" . nl
        , strstr "    , getTransitionsOfNFA = XMap.fromAscList " . plist 8 [ strstr "((" . showsPrec 0 (fst key) . strstr ", " . showsPrec 0 (snd key) . strstr "), XSet.fromAscList [" . ppunc ", " [ showsPrec 0 q | q <- Set.toAscList qs ] . strstr "])" | (key, qs) <- Map.toAscList deltas ] . nl
        , strstr "    , getMarkedQsOfNFA = XMap.fromAscList [" . ppunc ", " [ strstr "(" . showsPrec 0 q . strstr ", " . showsPrec 0 p . strstr ")" | (q, p) <- Map.toAscList markeds ] . strstr "]" . nl
        , strstr "    }"
        ]
    showList = undefined

instance Show DFA where
    showsPrec _ (DFA q0 qfs deltas markeds) = strcat
        [ strstr "DFA" . nl
        , strstr "    { getInitialQOfDFA = " . showsPrec 0 q0 . nl
        , strstr "    , getFinalQsOfDFA = XMap.fromAscList [" . ppunc ", " [ strstr "(" . showsPrec 0 q . strstr ", " . showsPrec 0 p . strstr ")" | (q, p) <- Map.toAscList qfs ] . strstr "]" . nl
        , strstr "    , getTransitionsOfDFA = XMap.fromAscList " . plist 8 [ ppunc ", " [ strstr "((" . showsPrec 0 q . strstr ", " . showsPrec 0 ch . strstr "), " . showsPrec 0 p . strstr ")" | ((q, ch), p) <- deltas ] | deltas <- split' (\x1 -> \x2 -> fst x1 == fst x2) (Map.toAscList deltas) ] . nl
        , strstr "    , getMarkedQsOfDFA = XMap.fromAscList " . plist 8 [ strstr "(" . showsPrec 0 q . strstr ", XSet.fromAscList [" . ppunc ", " [ showsPrec 0 p | p <- Set.toAscList ps ] . strstr "])" | (q, ps) <- Map.toAscList markeds ] . nl
        , strstr "    }"
        ]
    showList = undefined
