module Lib.Generator.PGS.Show where

import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.State.Strict
import Control.Monad.Trans.Writer.Strict
import Data.Functor.Identity
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Lib.Base
import Lib.Generator.PGS.Util

instance Outputable Associativity where
    makeOutput _ ALeft = strstr "left"
    makeOutput _ ARight = strstr "right"
    makeOutput _ ANone = strstr "none"

instance Outputable NSym where
    makeOutput 0 (NSApp ns1 ns2) = makeOutput 0 ns1 . strstr " " . makeOutput 1 ns2
    makeOutput 0 ns1 = makeOutput 1 ns1
    makeOutput 1 (NSVar nsv) = strstr nsv
    makeOutput 1 ns1 = makeOutput 2 ns1
    makeOutput _ ns1 = strstr "(" . makeOutput 0 ns1 . strstr ")"

instance Outputable TSym where
    makeOutput _ (TSEOF) = strstr "\\$"
    makeOutput _ (TSVar tsv) = strstr tsv

instance Outputable Sym where
    makeOutput _ (NS ns) = strstr "<" . makeOutput 0 ns . strstr ">"
    makeOutput _ (TS ts) = strstr "`" . makeOutput 0 ts . strstr "\'"

instance Outputable CFGrammar where
    makeOutput _ (CFGrammar start terminals productions) = strcat
        [ strstr "start-symbol: " . makeOutput 0 start . nl
        , strstr "terminal-symbols: " . plist 2 [ makeOutput 0 (TS t) . strstr " : " . makeOutput 0 assoc . strstr ", " . strstr (reverse (take 2 ("0" ++ reverse (show prec)))) | (t, (assoc, prec)) <- Map.toList terminals ] . nl
        , strstr "production-rules: " . plist 2 [ makeOutput 0 (NS lhs) . strstr " ::= " . ppunc " " (map (makeOutput 0) rhs) . strstr "; " . strstr (reverse (take 2 (reverse ("0" ++ show prec)))) | ((lhs, rhs), prec) <- Map.toList productions ] . nl
        ]

instance Outputable LR0Item where
    makeOutput _ (LR0Item lhs left right) = makeOutput 0 (NS lhs) . strstr " ::= " . ppunc " " (map (makeOutput 0) left) . strstr " . " . ppunc " " (map (makeOutput 0) right) . strstr ";"

instance Outputable Cannonical0 where
    makeOutput _ (Cannonical0 vertices root edges) = strcat
        [ strstr "vertices: " . plist 2 [ showsPrec 0 q . strstr ": " . plist 4 (map (makeOutput 0) (Set.toList items)) | (items, q) <- Map.toList vertices ] . nl
        , strstr "root: " . showsPrec 0 root . nl
        , strstr "edges: " . plist 2 [ strstr "(" . showsPrec 0 q . strstr ", " . makeOutput 0 sym . strstr ") +-> " . showsPrec 0 p | ((q, sym), p) <- Map.toList edges ] . nl
        ]

instance Outputable Action where
    makeOutput _ (Shift p) = strstr "SHIFT: " . showsPrec 0 p . strstr ";"
    makeOutput _ (Reduce (lhs, rhs)) = strstr "REDUCE: <" . makeOutput 0 lhs . strstr "> ::= " . ppunc " " (map (makeOutput 0) rhs) . strstr ";"
    makeOutput _ (Accept) = strstr "ACCEPT;"

instance Outputable LR1Parser where
    makeOutput _ (LR1Parser initS actionT reduceT) = strcat
        [ strstr "initS: " . showsPrec 0 initS . nl
        , strstr "actionT: " . plist 2 [ strstr "(" . showsPrec 0 q . strstr ", " . makeOutput 0 (TS t) . strstr ") +-> " . makeOutput 0 action | ((q, t), action) <- Map.toList actionT ] . nl
        , strstr "reduceT: " . plist 2 [ strstr "(" . showsPrec 0 q . strstr ", " . makeOutput 0 (NS nt) . showsPrec 0 p . strstr ";" | ((q, nt), p) <- Map.toList reduceT ] . nl
        ]
