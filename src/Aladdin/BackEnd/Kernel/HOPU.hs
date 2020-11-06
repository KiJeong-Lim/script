module Aladdin.BackEnd.Kernel.HOPU where

import Aladdin.BackEnd.Back
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
import Data.IORef
import Lib.Base

infix 3 +->

data Disagreement
    = Disagreement
        { getLHS :: TermNode
        , getRHS :: TermNode
        }
    deriving (Eq)

data HopuFail
    = DownFail
    | UpFail
    | OccursCheckFail
    | FlexRigidFail
    | RigidRigidFail
    | BindFail
    | NotAPattern
    deriving (Eq)

instance Show Disagreement where
    show = flip (showsPrec 0) ""
    showList = strcat . map (showsPrec 0)
    showsPrec _ (Disagreement { getLHS = lhs, getRHS = rhs }) = showsPrec 0 lhs . strstr " =?= " . showsPrec 0 rhs . nl

instance HasLVar Disagreement where
    getFreeLVars (Disagreement lhs rhs) = getFreeLVars lhs . getFreeLVars rhs
    applyBinding theta (Disagreement lhs rhs) = Disagreement (applyBinding theta lhs) (applyBinding theta rhs)

(+->) :: LogicVar -> TermNode -> VarBinding
v +-> t
    | t == LVar v = mempty
    | otherwise = VarBinding { getVarBinding = Map.singleton v t }

viewNestedNAbs :: TermNode -> (Int, TermNode)
viewNestedNAbs = go 0 where
    go :: Int -> TermNode -> (Int, TermNode)
    go n (NAbs t) = go (n + 1) t
    go n t = (n, t)

makeNestedNAbs :: Int -> TermNode -> TermNode
makeNestedNAbs n
    | n == 0 = id
    | n > 0 = makeNestedNAbs (n - 1) . NAbs
    | otherwise = undefined

isRigid :: TermNode -> Bool
isRigid (NCon c) = True
isRigid (NIdx i) = True
isRigid _ = False

insert' :: Eq a => a -> [a] -> [a]
insert' x xs
    | null xs = x : xs
    | x == head xs = xs
    | otherwise = head xs : insert' x (tail xs)

getNewLVar :: MonadIO m => Bool -> ScopeLevel -> StateT HopuEnv m TermNode
getNewLVar isty label = do
    uni <- liftIO newUnique
    let sym = if isty then mkTypeAtom (funique uni) else mkTermAtom (funique uni)
    env <- get
    put (env { getLabeling = enterID sym label (getLabeling env) })
    return (mkLVar sym)

substEnv :: VarBinding -> HopuEnv -> HopuEnv
substEnv theta (HopuEnv { getLabeling = labeling, getVBinding = binding }) = HopuEnv { getLabeling = labeling', getVBinding = binding' } where
    loop :: LogicVar -> ScopeLevel -> ScopeLevel
    loop v label = foldr min label
        [ label'
        | (v', t') <- Map.toList (getVarBinding binding)
        , v `Set.member` getFreeLVs t'
        , label' <- fromMaybeToList (Map.lookup v' (_VarLabel labeling))
        ]
    labeling' :: Labeling
    labeling' = labeling { _VarLabel = Map.mapWithKey loop (_VarLabel labeling) }
    binding' :: VarBinding
    binding' = theta <> binding

areAllDistinct :: Eq a => [a] -> Bool
areAllDistinct [] = True
areAllDistinct (x : xs) = not (elem x xs) && areAllDistinct xs

fromMaybeToList :: Maybe a -> [a]
fromMaybeToList Nothing = []
fromMaybeToList (Just x) = [x]

isPatternRespectTo :: LogicVar -> [TermNode] -> Labeling -> Bool
isPatternRespectTo v ts labeling = and
    [ all isRigid ts
    , areAllDistinct ts
    , and
        [ labelID labeling v < labelID labeling c
        | NCon c <- ts
        ]
    ]

down :: [TermNode] -> [TermNode] -> StateT HopuEnv (ExceptT HopuFail IO) [TermNode]
zs `down` ts = if downable then return indices else lift (throwE DownFail) where
    downable :: Bool
    downable = and
        [ areAllDistinct ts
        , all isRigid ts
        , areAllDistinct zs
        , all isRigid zs
        ]
    indices :: [TermNode]
    indices = map mkNIdx
        [ length ts - i
        | z <- zs
        , i <- fromMaybeToList (z `List.elemIndex` ts)
        ]

up :: [TermNode] -> LogicVar -> StateT HopuEnv (ExceptT HopuFail IO) [TermNode]
ts `up` y = if upable then findVisibles . getLabeling <$> get else lift (throwE UpFail) where
    upable :: Bool
    upable = and
        [ areAllDistinct ts
        , all isRigid ts
        ]
    findVisibles :: Labeling -> [TermNode]
    findVisibles labeling = map mkNCon
        [ c
        | NCon c <- ts
        , labelID labeling c <= labelID labeling y
        ]

bind :: LogicVar -> TermNode -> [TermNode] -> Int -> StateT HopuEnv (ExceptT HopuFail IO) TermNode
bind var = go . rewrite HNF where
    go :: TermNode -> [TermNode] -> Int -> StateT HopuEnv (ExceptT HopuFail IO) TermNode
    go rhs parameters lambda
        | (lambda', rhs') <- viewNestedNAbs rhs
        , lambda' > 0
        = do
            lhs' <- go rhs' parameters (lambda + lambda')
            return (makeNestedNAbs lambda' lhs')
        | (rhs_head, rhs_tail) <- unfoldlNApp rhs
        , isRigid rhs_head
        = do
            env <- get
            let labeling = getLabeling env
                get_lhs_head lhs_arguments
                    | NCon con <- rhs_head
                    , labelID labeling var >= labelID labeling con
                    = return rhs_head
                    | Just idx <- rhs_head `List.elemIndex` lhs_arguments
                    = return (mkNIdx (length lhs_arguments - idx))
                    | otherwise
                    = lift (throwE FlexRigidFail)
                foldbind [] = return []
                foldbind (rhs_tail_elements : rhs_tail) = do
                    lhs_tail_elements <- bind var rhs_tail_elements parameters lambda
                    env <- get
                    lhs_tail <- foldbind (applyBinding (getVBinding env) rhs_tail)
                    return (lhs_tail_elements : lhs_tail)
            lhs_head <- get_lhs_head ([ rewriteWithSusp param 0 lambda [] NF | param <- parameters ] ++ map mkNIdx [lambda, lambda - 1 .. 1])
            lhs_tail <- foldbind rhs_tail
            return (List.foldl' mkNApp lhs_head lhs_tail)
        | (LVar var', rhs_tail) <- unfoldlNApp rhs
        = if var == var'
            then lift (throwE OccursCheckFail)
            else do
                env <- get
                let labeling = getLabeling env
                    isty = isType var
                    lhs_arguments = [ rewriteWithSusp param 0 lambda [] NF | param <- parameters ] ++ map mkNIdx [lambda, lambda - 1 .. 1]
                    rhs_arguments = map (rewrite NF) rhs_tail
                    common_arguments = Set.toList (Set.fromList lhs_arguments `Set.intersection` Set.fromList rhs_arguments)
                if isPatternRespectTo var' rhs_arguments labeling
                    then do
                        (selected_lhs_arguments, selected_rhs_arguments) <- case labelID labeling var `compare` labelID labeling var' of
                            LT -> do
                                rhs_inner <- lhs_arguments `up` var'
                                lhs_inner <- rhs_inner `down` lhs_arguments
                                rhs_outer <- common_arguments `down` rhs_arguments
                                lhs_outer <- common_arguments `down` lhs_arguments
                                return (lhs_inner ++ lhs_outer, rhs_inner ++ rhs_outer)
                            geq -> do
                                lhs_inner <- rhs_arguments `up` var
                                rhs_inner <- lhs_inner `down` rhs_arguments
                                lhs_outer <- common_arguments `down` lhs_arguments
                                rhs_outer <- common_arguments `down` rhs_arguments
                                return (lhs_inner ++ lhs_outer, rhs_inner ++ rhs_outer)
                        common_head <- getNewLVar isty (labelID labeling var)
                        modify (substEnv (var' +-> makeNestedNAbs (length rhs_tail) (List.foldl' mkNApp common_head selected_rhs_arguments)))
                        return (List.foldl' mkNApp common_head selected_lhs_arguments)
                    else lift (throwE NotAPattern)
        | otherwise
        = lift (throwE BindFail)

mksubst :: LogicVar -> TermNode -> [TermNode] -> HopuEnv -> ExceptT HopuFail IO (Maybe HopuEnv)
mksubst var rhs parameters env = catchE (Just . snd <$> runStateT (go var (rewrite HNF rhs) parameters) env) handleErr where
    go :: LogicVar -> TermNode -> [TermNode] -> StateT HopuEnv (ExceptT HopuFail IO) ()
    go var rhs parameters
        | (lambda, rhs') <- viewNestedNAbs rhs
        , (LVar var', rhs_tail) <- unfoldlNApp rhs'
        , var == var'
        = do
            env <- get
            let labeling = getLabeling env
                isty = isType var
                n = length parameters + lambda
                lhs_arguments = [ rewriteWithSusp param 0 lambda [] NF | param <- parameters ] ++ map mkNIdx [lambda, lambda - 1 .. 1] 
                rhs_arguments = map (rewrite NF) rhs_tail
                common_arguments = [ mkNIdx (n - i) | i <- [0, 1 .. n - 1], lhs_arguments !! i == rhs_arguments !! i ]
            if isPatternRespectTo var' rhs_arguments labeling
                then do
                    common_head <- getNewLVar isty (labelID labeling var)
                    modify (substEnv (var' +-> makeNestedNAbs n (List.foldl' mkNApp common_head common_arguments)))
                else lift (throwE NotAPattern)
        | otherwise
        = do
            env <- get
            let labeling = getLabeling env
                n = length parameters
                lhs_arguments = map (rewrite NF) parameters
            if isPatternRespectTo var lhs_arguments labeling
                then do
                    lhs <- bind var rhs parameters 0
                    modify (substEnv (var +-> makeNestedNAbs n lhs))
                else lift (throwE NotAPattern)
    handleErr :: HopuFail -> ExceptT HopuFail IO (Maybe HopuEnv)
    handleErr NotAPattern = return Nothing
    handleErr err = throwE err

simplify :: IORef Bool -> [Disagreement] -> StateT HopuEnv (ExceptT HopuFail IO) [Disagreement]
simplify changed = go where
    go :: [Disagreement] -> StateT HopuEnv (ExceptT HopuFail IO) [Disagreement]
    go [] = return []
    go (Disagreement lhs rhs : disagreements) = aux (rewrite HNF lhs) (rewrite HNF rhs) where
        aux :: TermNode -> TermNode -> StateT HopuEnv (ExceptT HopuFail IO) [Disagreement]
        aux lhs rhs
            | (lambda1, lhs') <- viewNestedNAbs lhs
            , (lambda2, rhs') <- viewNestedNAbs rhs
            , lambda1 > 0 && lambda2 > 0
            = case lambda1 `compare` lambda2 of
                LT -> aux lhs' (makeNestedNAbs (lambda2 - lambda1) rhs')
                EQ -> aux lhs' rhs'
                GT -> aux (makeNestedNAbs (lambda1 - lambda2) lhs') rhs'
            | (lambda1, lhs') <- viewNestedNAbs lhs
            , (rhs_head, rhs_tail) <- unfoldlNApp rhs
            , lambda1 > 0 && isRigid rhs_head
            = aux lhs' (List.foldl' mkNApp rhs (map mkNIdx [lambda1, lambda1 - 1 .. 1]))
            | (lhs_head, lhs_tail) <- unfoldlNApp lhs
            , (lambda2, rhs') <- viewNestedNAbs rhs
            , isRigid lhs_head && lambda2 > 0
            = aux (List.foldl' mkNApp lhs (map mkNIdx [lambda2, lambda2 - 1 .. 1])) rhs'
            | (lhs_head, lhs_tail) <- unfoldlNApp lhs
            , (rhs_head, rhs_tail) <- unfoldlNApp rhs
            , isRigid lhs_head && isRigid rhs_head
            = if lhs_head == rhs_head && length lhs_tail == length rhs_tail
                then go (zipWith Disagreement lhs_tail rhs_tail ++ disagreements)
                else lift (throwE RigidRigidFail)
            | (LVar var, parameters) <- unfoldlNApp lhs
            = do
                env <- get
                output <- lift (mksubst var rhs parameters env)
                case output of
                    Nothing -> solveNext
                    Just env -> do
                        put env
                        liftIO (writeIORef changed True)
                        go (applyBinding (getVBinding env) disagreements)
            | (LVar var, parameters) <- unfoldlNApp rhs
            = do
                env <- get
                output <- lift (mksubst var lhs parameters env)
                case output of
                    Nothing -> solveNext
                    Just env -> do
                        put env
                        liftIO (writeIORef changed True)
                        go (applyBinding (getVBinding env) disagreements)
            | otherwise
            = solveNext
            where
                solveNext :: StateT HopuEnv (ExceptT HopuFail IO) [Disagreement]
                solveNext = do
                    disagreements' <- go disagreements
                    env <- get
                    return (insert' (applyBinding (getVBinding env) (Disagreement lhs rhs)) disagreements)

runHOPU :: [Disagreement] -> Labeling -> IO (Maybe (HopuEnv, [Disagreement]))
runHOPU disagreements labeling = do
    changed <- newIORef False
    let initEnv = HopuEnv { getLabeling = labeling, getVBinding = mempty }
        loop disagreements = do
            disagreements' <- simplify changed disagreements
            has_changed <- liftIO (readIORef changed)
            if has_changed
                then do
                    liftIO (writeIORef changed False)
                    loop disagreements'
                else return disagreements'
    output <- runExceptT (runStateT (loop disagreements) initEnv)
    case output of
        Left err -> return Nothing
        Right (disagreements', env') -> return (Just (env', disagreements'))
