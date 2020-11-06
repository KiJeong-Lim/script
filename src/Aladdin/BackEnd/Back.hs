module Aladdin.BackEnd.Back where

import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.State.Strict
import Data.Functor.Identity
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Unique
import Lib.Base

type DeBruijn = Int

type LogicVar = Atom VI

type Constant = Atom CI

type SuspEnv = [SuspItem]

type ScopeLevel = Int

data Atom id
    = Atom
        { isType :: Bool
        , _ID :: id
        }
    deriving ()

data VI
    = VI_Unique Unique
    | VI_Named String
    deriving (Eq, Ord)

data CI
    = CI_Unique Unique
    | CI_Named String
    | CI_Lambda
    | CI_If
    | CI_True
    | CI_Fail
    | CI_Cut
    | CI_And
    | CI_Or
    | CI_Imply
    | CI_Sigma
    | CI_Pi
    | CI_ChrL Char
    | CI_NatL Integer
    | CI_BuiltIn BuiltIn
    deriving (Eq, Ord)

data BuiltIn
    = BI_o
    | BI_arrow
    | BI_list
    | BI_char
    | BI_nat
    | BI_cons
    | BI_nil
    | BI_plus
    | BI_mult
    | BI_equal
    | BI_leq
    | BI_geq
    | BI_is_var
    | BI_assert
    deriving (Eq, Ord)

data TermNode
    = LVar LogicVar
    | NCon Constant
    | NIdx DeBruijn
    | NApp TermNode TermNode
    | NAbs TermNode
    | Susp
        { getSubstitutee :: TermNode
        , getOL :: Int
        , getNL :: Int
        , getSuspEnv :: SuspEnv
        }
    deriving (Eq, Ord)

data SuspItem
    = Dummy Int
    | Binds TermNode Int
    deriving (Eq, Ord)

data ReductionOption
    = WHNF
    | HNF
    | NF
    deriving (Eq)

data Labeling
    = Labeling
        { _ConLabel :: Map.Map Constant ScopeLevel
        , _VarLabel :: Map.Map LogicVar ScopeLevel
        }
    deriving ()

data HopuEnv
    = HopuEnv
        { getLabeling :: Labeling
        , getVBinding :: VarBinding
        }
    deriving ()

newtype VarBinding
    = VarBinding { getVarBinding :: Map.Map LogicVar TermNode }
    deriving (Eq)

data ShowNode
    = ShowIVar Int
    | ShowLVar String
    | ShowTVar String
    | ShowIAbs Int ShowNode
    | ShowIApp ShowNode ShowNode
    | ShowNatL Integer
    | ShowChrL Char
    | ShowStrL String
    | ShowList [ShowNode]
    | ShowDCon String
    | ShowTCon String
    | ShowTApp ShowNode ShowNode
    | ShowOper ShowNode String ShowNode
    deriving ()

class IsID id where
    funique :: Unique -> id
    enterID :: Atom id -> ScopeLevel -> Labeling -> Labeling
    renewID :: Atom id -> ScopeLevel -> Labeling -> Labeling
    labelID :: Labeling -> Atom id -> ScopeLevel

class HasLVar expr where
    getFreeLVars :: expr -> Set.Set LogicVar -> Set.Set LogicVar
    applyBinding :: VarBinding -> expr -> expr

instance Eq id => Eq (Atom id) where
    Atom _ id1 == Atom _ id2 = id1 == id2

instance Ord id => Ord (Atom id) where
    Atom _ id1 `compare` Atom _ id2 = id1 `compare` id2

instance Show id => Show (Atom id) where
    show = flip (showsPrec 0) ""
    showList = showList . map _ID
    showsPrec prec = showsPrec prec . _ID

instance IsID VI where
    funique atom = VI_Unique atom
    enterID atom level labeling = labeling { _VarLabel = Map.insert atom level (_VarLabel labeling) }
    renewID atom level labeling = labeling { _VarLabel = Map.update (\_ -> Just level) atom (_VarLabel labeling) }
    labelID labeling atom = maybe 0 id (Map.lookup atom (_VarLabel labeling))

instance Show VI where
    show = flip (showsPrec 0) ""
    showList = undefined
    showsPrec _ = go where
        go :: VI -> String -> String
        go (VI_Named str) = strstr str
        go (VI_Unique uni) = strstr "V_" . showsPrec 0 (hashUnique uni)

instance IsID CI where
    funique atom = CI_Unique atom
    enterID atom level labeling = labeling { _ConLabel = Map.insert atom level (_ConLabel labeling) }
    renewID atom level labeling = labeling { _ConLabel = Map.update (\_-> Just level) atom (_ConLabel labeling) }
    labelID labeling atom = maybe 0 id (Map.lookup atom (_ConLabel labeling))

instance Show CI where
    show = flip (showsPrec 0) ""
    showList = undefined
    showsPrec _ = go where
        go :: CI -> String -> String
        go (CI_Unique uni) = strstr "c_" . showsPrec 0 (hashUnique uni)
        go (CI_Named str) = strstr str
        go CI_Lambda = strstr "__lambda"
        go CI_If = strstr "__if"
        go CI_True = strstr "__true"
        go CI_Fail = strstr "__fail"
        go CI_Cut = strstr "__cut"
        go CI_And = strstr "__and"
        go CI_Or = strstr "__or"
        go CI_Imply = strstr "__imply"
        go CI_Sigma = strstr "__sigma"
        go CI_Pi = strstr "__pi"
        go (CI_ChrL chr) = showsPrec 0 chr
        go (CI_NatL nat) = showsPrec 0 nat
        go (CI_BuiltIn built_in) = showsPrec 0 built_in

instance Show BuiltIn where
    show = flip (showsPrec 0) ""
    showList = undefined
    showsPrec _ = go where
        go :: BuiltIn -> String -> String
        go BI_o = strstr "__o"
        go BI_arrow = strstr "__arrow"
        go BI_list = strstr "__list"
        go BI_char = strstr "__char"
        go BI_nat = strstr "__nat"
        go BI_nil = strstr "__nil"
        go BI_cons = strstr "__cons"
        go BI_plus = strstr "__plus"
        go BI_mult = strstr "__mult"
        go BI_leq = strstr "__leq"
        go BI_geq = strstr "__geq"
        go BI_equal = strstr "__equal"
        go BI_is_var = strstr "__is_var"
        go BI_assert = strstr "__assert"

instance Read TermNode where
    readsPrec = flip go [] where
        cond1 :: Char -> Bool
        cond1 ch = ch `elem` ['a' .. 'z'] || ch `elem` ['0' .. '9'] || ch == '_'
        cond2 :: Char -> Bool
        cond2 ch = ch `elem` ['A' .. 'Z'] || ch `elem` ['a' .. 'z'] || ch `elem` ['0' .. '9']
        readCon :: String -> [(String, String)]
        readCon (ch : str)
            | ch `elem` ['a' .. 'z'] = return (ch : takeWhile cond1 str, dropWhile cond1 str)
        readCon _ = []
        readVar :: String -> [(String, String)]
        readVar (ch : str)
            | ch `elem` ['A' .. 'Z'] = return (ch : takeWhile cond2 str, dropWhile cond2 str)
        readVar _ = []
        installVar :: [String] -> String -> TermNode
        installVar env str = case str `List.elemIndex` env of
            Nothing -> mkLVar (mkTermAtom (VI_Named str))
            Just i -> mkNIdx (i + 1)
        many :: (String -> [(a, String)]) -> (String -> [([a], String)])
        many p str0 = concat
            [ do
                (x, str1) <- p str0
                (xs, str2) <- many p str1
                return (x : xs, str2)
            , return ([], str0)
            ]
        go :: Int -> [String] -> String -> [(TermNode, String)]
        go 0 env str0 = concat
            [ do
                (str, '\\' : ' ' : str1) <- readVar str0
                (t, str2) <- go 0 (str : env) str1
                return (mkNAbs t, str2)
            , go 1 env str0
            ]
        go 1 env str0 = do
            (t, str1) <- go 2 env str0
            (ts, str2) <- many (getArgs env) str1
            return (List.foldl' mkNApp t ts, str2)
        go 2 env str0 = concat
            [ do
                (str, str1) <- readCon str0
                return (mkNCon (mkTermAtom (CI_Named str)), str1)
            , do
                (str, str1) <- readVar str0
                return (installVar env str, str1)
            ]
        go _ env ('(' : str0) = do
            (t, ')' : str1) <- go 0 env str0
            return (t, str1)
        go _ _ _ = []
        getArgs :: [String] -> String -> [(TermNode, String)]
        getArgs env (' ' : str0) = go 2 env str0
        getArgs _ _ = []
    readList = undefined

instance Show TermNode where
    show = flip (showsPrec 0) ""
    showList [] = id
    showList (t : ts) = showsPrec 0 t . strstr ";" . nl . showList ts
    showsPrec prec = showsPrec prec . showTerm

instance HasLVar TermNode where
    getFreeLVars (LVar v) = Set.insert v
    getFreeLVars (NCon c) = id
    getFreeLVars (NIdx i) = id
    getFreeLVars (NApp t1 t2) = getFreeLVars t1 . getFreeLVars t2
    getFreeLVars (NAbs t) = getFreeLVars t
    getFreeLVars (Susp t ol nl env) = getFreeLVars (rewriteWithSusp t ol nl env HNF)
    applyBinding = flatten

instance HasLVar a => HasLVar [a] where
    getFreeLVars = flip (foldr getFreeLVars)
    applyBinding = map . applyBinding

instance HasLVar b => HasLVar (a, b) where
    getFreeLVars = getFreeLVars . snd
    applyBinding = fmap . applyBinding

instance HasLVar a => HasLVar (Map.Map k a) where
    getFreeLVars = getFreeLVars . Map.elems
    applyBinding = Map.map . applyBinding

instance Semigroup VarBinding where
    theta2 <> theta1 = map21 `seq` VarBinding map21 where
        map1 :: Map.Map LogicVar TermNode
        map1 = getVarBinding theta1
        map2 :: Map.Map LogicVar TermNode
        map2 = getVarBinding theta2
        map21 :: Map.Map LogicVar TermNode
        map21 = applyBinding theta2 map1 `Map.union` map2

instance Monoid VarBinding where
    mempty = map0 `seq` VarBinding map0 where
        map0 :: Map.Map LogicVar TermNode
        map0 = Map.empty

instance Show ShowNode where
    show = flip (showsPrec 0) ""
    showList [] = strstr "[]"
    showList (sn : sns) = strstr "[" . go sn sns where
        go :: ShowNode -> [ShowNode] -> String -> String
        go sn1 [] rest = showsPrec 5 sn1 ("]" ++ rest)
        go sn1 (sn2 : sns) rest = showsPrec 5 sn1 (", " ++ go sn2 sns rest)
    showsPrec prec = go where        
        parenthesize :: Int -> (String -> String) -> String -> String
        parenthesize prec' delta rest
            | prec > prec' = "(" ++ delta (")" ++ rest)
            | otherwise = delta rest
        go :: ShowNode -> String -> String
        go (ShowIAbs v sn) = parenthesize 0 (strstr "W_" . showsPrec 0 v . strstr "\\ " . showsPrec 0 sn)
        go (ShowOper sn1 "__if" sn2) = parenthesize 0 (showsPrec 5 sn1 . strstr " :- " . showsPrec 1 sn2)
        go (ShowOper sn1 "__or" sn2) = parenthesize 1 (showsPrec 1 sn1 . strstr "; " . showsPrec 2 sn2)
        go (ShowOper sn1 "__imply" sn2) = parenthesize 2 (showsPrec 5 sn1 . strstr " => " . showsPrec 2 sn2)
        go (ShowOper sn1 "__comma" sn2) = parenthesize 3 (showsPrec 3 sn1 . strstr ", " . showsPrec 4 sn2)
        go (ShowOper sn1 "__arrow" sn2) = parenthesize 4 (showsPrec 5 sn1 . strstr " -> " . showsPrec 4 sn2)
        go (ShowOper sn1 "__equal" sn2) = parenthesize 4 (showsPrec 5 sn1 . strstr " = " . showsPrec 5 sn2)
        go (ShowOper sn1 "__leq" sn2) = parenthesize 4 (showsPrec 5 sn1 . strstr " =< " . showsPrec 5 sn2)
        go (ShowOper sn1 "__geq" sn2) = parenthesize 4 (showsPrec 5 sn1 . strstr " >= " . showsPrec 5 sn2)
        go (ShowOper sn1 "__plus" sn2) = parenthesize 5 (showsPrec 5 sn1 . strstr " + " . showsPrec 6 sn2)
        go (ShowOper sn1 "__mult" sn2) = parenthesize 6 (showsPrec 6 sn1 . strstr " * " . showsPrec 7 sn2)
        go (ShowOper sn1 "__cons" sn2) = parenthesize 7 (showsPrec 8 sn1 . strstr " :: " . showsPrec 7 sn2)
        go (ShowTApp sn1 sn2) = parenthesize 9 (showsPrec 9 sn1 . strstr " " . showsPrec 10 sn2)
        go (ShowIApp sn1 sn2) = parenthesize 9 (showsPrec 9 sn1 . strstr " " . showsPrec 10 sn2)
        go (ShowTCon c) = parenthesize 10 (showsPrec 0 c)
        go (ShowDCon c) = parenthesize 10 (showsPrec 0 c)
        go (ShowIVar v) = parenthesize 10 (strstr "W_" . showsPrec 0 v)
        go (ShowLVar v) = parenthesize 10 (strstr v)
        go (ShowTVar v) = parenthesize 10 (strstr v)
        go (ShowStrL str) = parenthesize 10 (showsPrec 0 str)
        go (ShowChrL chr) = parenthesize 10 (showsPrec 0 chr)
        go (ShowNatL nat) = parenthesize 10 (showsPrec 0 nat)
        go (ShowList sns) = parenthesize 10 (showList sns)

getFreeLVs :: HasLVar expr => expr -> Set.Set LogicVar
getFreeLVs = flip getFreeLVars Set.empty

mkTermAtom :: id -> Atom id
mkTermAtom id1 = id1 `seq` Atom { isType = False, _ID = id1 }

mkTypeAtom :: id -> Atom id
mkTypeAtom id1 = id1 `seq` Atom { isType = True, _ID = id1 }

mkLVar :: LogicVar -> TermNode
mkLVar v = v `seq` LVar v

mkNCon :: Constant -> TermNode
mkNCon c = c `seq` NCon c

mkNIdx :: DeBruijn -> TermNode
mkNIdx i = i `seq` NIdx i

mkNApp :: TermNode -> TermNode -> TermNode
mkNApp t1 t2 = t1 `seq` t2 `seq` NApp t1 t2

mkNAbs :: TermNode -> TermNode
mkNAbs t = t `seq` NAbs t

mkSusp :: TermNode -> Int -> Int -> SuspEnv -> TermNode
mkSusp t 0 0 [] = t
mkSusp t ol nl (item : env) = t `seq` item `seq` Susp t ol nl (item : env)

mkDummy :: Int -> SuspItem
mkDummy l = l `seq` Dummy l

mkBinds :: TermNode -> Int -> SuspItem
mkBinds t l = t `seq` l `seq` Binds t l

lensForSusp :: (TermNode -> TermNode) -> SuspEnv -> SuspEnv
lensForSusp delta = map go where
    go :: SuspItem -> SuspItem
    go (Dummy l) = mkDummy l
    go (Binds t l) = mkBinds (delta t) l

flatten :: VarBinding -> TermNode -> TermNode
flatten (VarBinding { getVarBinding = mapsto }) = go where
    go :: TermNode -> TermNode
    go (LVar v) = case Map.lookup v mapsto of
        Nothing -> mkLVar v
        Just t -> go t
    go (NCon c) = mkNCon c
    go (NIdx i) = mkNIdx i
    go (NApp t1 t2) = mkNApp (go t1) (go t2)
    go (NAbs t) = mkNAbs (go t)
    go (Susp t ol nl env) = mkSusp (go t) ol nl (lensForSusp go env)

unfoldlNApp :: TermNode -> (TermNode, [TermNode])
unfoldlNApp = flip go [] where
    go :: TermNode -> [TermNode] -> (TermNode, [TermNode])
    go (NApp t1 t2) ts = go t1 (t2 : ts)
    go t ts = (t, ts)

rewriteWithSusp :: TermNode -> Int -> Int -> SuspEnv -> ReductionOption -> TermNode
rewriteWithSusp (LVar v) ol nl env option
    = mkLVar v
rewriteWithSusp (NCon c) ol nl env option
    = mkNCon c
rewriteWithSusp (NIdx i) ol nl env option
    | i > ol = mkNIdx (i - ol + nl)
    | i >= 1 = case env !! (i - 1) of
        Dummy l -> mkNIdx (nl - l)
        Binds t l -> rewriteWithSusp t 0 (nl - l) [] option
    | otherwise = undefined
rewriteWithSusp (NApp t1 t2) ol nl env option
    = case rewriteWithSusp t1 ol nl env WHNF of
        NAbs (Susp t1' ol1' nl1' (Dummy nl1 : env1'))
            | ol1' > 0 && nl1 + 1 == nl1' -> rewriteWithSusp t1' ol1' nl1 (mkBinds (mkSusp t2 ol nl env) nl1 : env1') option
        NAbs t1' -> rewriteWithSusp t1' 1 0 [mkBinds (mkSusp t2 ol nl env) 0] option
        t1' -> case option of
            NF -> mkNApp (rewriteWithSusp t1' 0 0 [] option) (rewriteWithSusp t2 ol nl env option)
            HNF -> mkNApp (rewriteWithSusp t1' 0 0 [] option) (mkSusp t2 ol nl env)
            WHNF -> mkNApp t1' (mkSusp t2 ol nl env)
rewriteWithSusp (NAbs t1) ol nl env option
    | option == WHNF = mkNAbs (mkSusp t1 (ol + 1) (nl + 1) (mkDummy nl : env))
    | otherwise = mkNAbs (rewriteWithSusp t1 (ol + 1) (nl + 1) (mkDummy nl : env) option)
rewriteWithSusp (Susp t ol nl env) ol' nl' env' option
    | ol == 0 && nl == 0 = rewriteWithSusp t ol' nl' env' option
    | ol' == 0 = rewriteWithSusp t ol (nl + nl') env option
    | otherwise = case rewriteWithSusp t ol nl env option of
        NAbs t'
            | option == WHNF -> mkNAbs (mkSusp t' (ol' + 1) (nl' + 1) (mkDummy nl' : env'))
            | otherwise -> mkNAbs (rewriteWithSusp t' (ol' + 1) (nl' + 1) (mkDummy nl' : env') option)
        t' -> rewriteWithSusp t' ol' nl' env' option

rewrite :: ReductionOption -> TermNode -> TermNode
rewrite option t = rewriteWithSusp t 0 0 [] option

showTerm :: TermNode -> ShowNode
showTerm = fst . runIdentity . uncurry (runStateT . format . erase) . runIdentity . flip runStateT 1 . make [] . rewrite NF where
    isTy :: ShowNode -> Bool
    isTy (ShowTVar _) = True
    isTy (ShowTCon _) = True
    isTy (ShowTApp _ _) = True
    isTy (ShowOper _ "->" _) = True
    isTy _ = False
    make :: [Int] -> TermNode -> StateT Int Identity ShowNode
    make vs (NAbs t) = do
        v <- get
        let v' = v + 1
        put v'
        t_rep <- make (v : vs) t
        return (ShowIAbs v t_rep)
    make vs (NCon c)
        | isType c = case _ID c of
            CI_Unique uni -> return (ShowTCon ("tc_" ++ show (hashUnique uni)))
            CI_Named str -> return (ShowTCon str)
            ci -> return (ShowTCon (show ci))
        | otherwise = case _ID c of
            CI_Unique uni -> return (ShowDCon ("c_" ++ show (hashUnique uni)))
            CI_Named str -> return (ShowDCon str)
            CI_NatL nat -> return (ShowNatL nat)
            CI_ChrL chr -> return (ShowChrL chr)
            ci -> return (ShowDCon (show ci))
    make vs (NApp t1 t2) = do
        t1_rep <- make vs t1
        t2_rep <- make vs t2
        if isTy t1_rep
            then return (ShowTApp t1_rep t2_rep)
            else return (ShowIApp t1_rep t2_rep)
    make vs (NIdx i) = return (ShowIVar (vs !! (i - 1)))
    make vs (LVar v)
        | isType v = case _ID v of
            VI_Unique uni -> return (ShowTVar ("TV_" ++ show (hashUnique uni)))
            VI_Named str -> return (ShowTVar str)
        | otherwise = case _ID v of
            VI_Unique uni -> return (ShowLVar ("V_" ++ show (hashUnique uni)))
            VI_Named str -> return (ShowLVar str)
    erase :: ShowNode -> ShowNode
    erase (ShowIApp (ShowDCon "__nil") (ShowTCon "char")) = ShowStrL ""
    erase (ShowTCon c) = ShowTCon c
    erase (ShowTApp t1 t2) = ShowIApp (erase t1) (erase t2)
    erase (ShowIVar v) = ShowIVar v
    erase (ShowLVar v) = ShowLVar v
    erase (ShowTVar v) = ShowTVar v
    erase (ShowIAbs v t) = ShowIAbs v (erase t)
    erase (ShowIApp t1 t2)
        | isTy t2 = erase t1
        | otherwise = ShowIApp (erase t1) (erase t2)
    erase (ShowChrL chr) = ShowChrL chr
    erase (ShowDCon c) = ShowDCon c
    format :: ShowNode -> StateT Int Identity ShowNode
    format (ShowDCon "__nil") = return (ShowList [])
    format (ShowIApp (ShowIApp (ShowDCon "__cons") (ShowChrL chr)) sn2) = do
        sn2' <- format sn2
        case sn2' of
            ShowStrL str -> return (ShowStrL (chr : str))
            _ -> return (ShowOper (ShowChrL chr) "__cons" sn2')
    format (ShowIApp (ShowIApp (ShowDCon "__cons") sn1) sn2) = do
        sn1' <- format sn1
        sn2' <- format sn2
        case sn2' of
            ShowList sns' -> return (ShowList (sn1' : sns'))
            _ -> return (ShowOper sn1' "__cons" sn2')
    format (ShowIApp (ShowIApp (ShowDCon c) sn1) sn2)
        | c `elem` infixdcons = do
            sn1' <- format sn1
            sn2' <- format sn2
            return (ShowOper sn1' c sn2')
    format (ShowIApp (ShowDCon c) sn1)
        | c `elem` infixdcons = do
            sn1' <- format sn1
            v <- get
            put (v + 1)
            return (ShowIAbs v (ShowOper sn1' c (ShowIVar v)))
    format (ShowDCon c)
        | c `elem` infixdcons = do
            v <- get
            put (v + 2)
            return (ShowIAbs v (ShowIAbs (v + 1) (ShowOper (ShowIVar (v + 1)) c (ShowIVar (v + 1)))))
    format (ShowDCon c) = return (ShowDCon (maybe c id (Map.lookup c mapsReservedConToRep)))
    format (ShowIVar v) = return (ShowIVar v)
    format (ShowLVar v) = return (ShowLVar v)
    format (ShowTVar v) = return (ShowTVar v)
    format (ShowIAbs v sn) = do
        sn' <- format sn
        return (ShowIAbs v sn')
    format (ShowIApp sn1 sn2) = do
        sn1' <- format sn1
        sn2' <- format sn2
        return (ShowIApp sn1' sn2')
    format (ShowChrL chr) = return (ShowChrL chr)
    format (ShowStrL str) = return (ShowStrL str)
    format (ShowList sns) = do
        sns' <- mapM format sns
        return (ShowList sns')
    format (ShowTApp (ShowTApp (ShowTCon "__arrow") sn1) sn2) = do
        sn1' <- format sn1
        sn2' <- format sn2
        return (ShowOper sn1' "__arrow" sn2')
    format (ShowTApp sn1 sn2) = do
        sn1' <- format sn1
        sn2' <- format sn2
        return (ShowTApp sn1' sn2')
    format (ShowTCon c) = return (ShowTCon (maybe c id (Map.lookup c mapsReservedConToRep)))
    infixdcons :: [String]
    infixdcons = concat
        [ map show
            [ CI_If
            , CI_And
            , CI_Or
            , CI_Imply
            ]
        , map show
            [ BI_plus
            , BI_mult
            , BI_leq
            , BI_geq
            , BI_equal
            ]
        ]
    mapsReservedConToRep :: Map.Map String String
    mapsReservedConToRep = Map.fromList
        [ ("__pi", "pi")
        , ("__sigma", "sigma")
        , ("__cut", "!")
        , ("__fail", "fail")
        , ("__true", "true")
        , ("__is_var", "is_var")
        , ("__assert", "assert")
        , ("__o", "o")
        , ("__list", "list")
        , ("__char", "char")
        , ("__nat", "nat")
        ]
