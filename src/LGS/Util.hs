module LGS.Util where

import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.State.Strict
import Control.Monad.Trans.Writer.Strict
import Data.Functor.Identity
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Lib.Base
import Lib.Text.Ppr

type ErrMsg = String

type ParserS = Int

type CharSetVar = String

type RegExVar = String

type HsCode = [String]

type CharSetEnv = Map.Map CharSetVar CharSet

type RegExEnv = Map.Map RegExVar RegEx

data CharSet
    = CsVar CharSetVar
    | CsSingle Char
    | CsEnum Char Char
    | CsUnion CharSet CharSet
    | CsDiff CharSet CharSet
    | CsUniv
    deriving (Eq, Show)

data RegEx
    = ReVar RegExVar
    | ReZero
    | ReUnion RegEx RegEx
    | ReWord String
    | ReConcat RegEx RegEx
    | ReStar RegEx
    | ReDagger RegEx
    | ReQuest RegEx
    | ReCharSet CharSet
    deriving (Eq, Show)

data NFA
    = NFA
        { getInitialQOfNFA :: ParserS
        , getFinalQsOfNFA :: Set.Set ParserS
        , getTransitionsOfNFA :: Map.Map (ParserS, Maybe Char) (Set.Set ParserS)
        , getMarkedQsOfNFA :: Map.Map ParserS ParserS
        }
    deriving (Eq)

data DFA
    = DFA
        { getInitialQOfDFA :: ParserS
        , getFinalQsOfDFA :: Map.Map ParserS ParserS
        , getTransitionsOfDFA :: Map.Map (ParserS, Char) ParserS
        , getMarkedQsOfDFA :: Map.Map ParserS (Set.Set ParserS)
        }
    deriving (Eq)

data XBlock
    = HsHead HsCode
    | HsTail HsCode
    | CsVDef CharSetVar CharSet
    | ReVDef RegExVar RegEx
    | XMatch (RegEx, Maybe RegEx) (Maybe HsCode)
    | Target { getTokenType :: String, getLexerName :: String }
    deriving (Show)

instance Outputable CharSet where
    pprint 0 (CsDiff chs1 chs2) = pprint 0 chs1 . strstr " \\ " . pprint 2 chs2
    pprint 0 chs = pprint 1 chs
    pprint 1 (CsUnion chs1 chs2) = pprint 1 chs1 . strstr " " . pprint 2 chs2
    pprint 1 chs = pprint 2 chs
    pprint 2 (CsVar var) = strstr "$" . strstr var
    pprint 2 (CsSingle ch1) = showsPrec 0 ch1
    pprint 2 (CsEnum ch1 ch2) = showsPrec 0 ch1 . strstr "-" . showsPrec 0 ch2
    pprint 2 chs = pprint 3 chs
    pprint _ chs = strstr "(" . pprint 0 chs . strstr ")"

instance Outputable RegEx where
    pprint 0 (ReUnion re1 re2) = pprint 0 re1 . strstr " + " . pprint 1 re2
    pprint 0 re = pprint 1 re
    pprint 1 (ReConcat re1 re2) = pprint 1 re1 . strstr " " . pprint 2 re2
    pprint 1 re = pprint 2 re
    pprint 2 (ReStar re1) = pprint 2 re1 . strstr "*"
    pprint 2 (ReDagger re1) = pprint 2 re1 . strstr "+"
    pprint 2 (ReQuest re1) = pprint 2 re1 . strstr "?"
    pprint 2 re = pprint 3 re
    pprint 3 (ReCharSet chs1) = strstr "[" . pprint 0 chs1 . strstr "]"
    pprint 3 (ReWord str1) = pprintString str1
    pprint 3 (ReZero) = strstr "()"
    pprint 3 (ReVar var) = strstr "$" . strstr var
    pprint 3 re = pprint 4 re
    pprint _ re = strstr "(" . pprint 0 re . strstr ")"
