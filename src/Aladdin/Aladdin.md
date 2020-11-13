# Implementation

## Front

## Back

- TermNode:

```haskell
type SuspEnv = [SuspItem]

data TermNode
    = LVar LogicVar
    | NCon Constant
    | NIdx DeBruijn
    | NApp TermNode TermNode
    | NAbs TermNode
    | Susp Int Int SuspEnv
    deriving (Eq, Ord)

data SuspItem
    = Binds TermNode Int
    | Dummy Int
    deriving (Eq, Ord)

data ReduceOption
    = WHNF
    | HNF
    | NF
    deriving (Eq)

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
```
