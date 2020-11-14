module Aladdin.Back.Kernel.Runtime.Transition where

import Aladdin.Back.Base.Constant
import Aladdin.Back.Base.Labeling
import Aladdin.Back.Base.TermNode
import Aladdin.Back.Base.TermNode.Show
import Aladdin.Back.Base.TermNode.Util
import Aladdin.Back.Base.VarBinding
import Aladdin.Back.Kernel.Constraint
import Aladdin.Back.Kernel.Disagreement
import Aladdin.Back.Kernel.KernelErr
import Aladdin.Back.Kernel.Runtime.LogicalOperator
import Aladdin.Back.Kernel.Runtime.Util
import Aladdin.Back.Kernel.Solver.Util
import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.State.Strict
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Lib.Base

showStackItem :: Indentation -> (Context, [Cell]) -> String -> String
showStackItem space (ctx, cells) = strcat
    [ pindent space . strstr "- progressings = " . plist (space + 4) [ strstr "?- " . showsPrec 0 goal | Cell facts level goal <- cells ] . nl
    , pindent space . strstr "- context = Context" . nl
    , pindent (space + 4) . strstr "{ " . strstr "_TotalVarBinding = " . plist (space + 8) [ showsPrec 0 (LVar v) . strstr " +-> " . showsPrec 0 t | (v, t) <- Map.toList (unVarBinding (_TotalVarBinding ctx)) ] . nl
    , pindent (space + 4) . strstr ", " . strstr "_LeftConstraints = " . plist (space + 8) [ showsPrec 0 constraint | constraint <- _LeftConstraints ctx ] . nl
    , pindent (space + 4) . strstr "} " . nl
    ]

showsCurrentState :: Context -> [Cell] -> Stack -> String -> String
showsCurrentState ctx cells stack = strcat
    [ strstr "* The top of the stack is:" . nl
    , showStackItem 4 (ctx, cells) . nl
    , strstr "* The rest of the stack is:" . nl
    , strcat
        [ strcat
            [ pindent 2 . strstr "- #[ " . showsPrec 0 i . strstr "]:" . nl
            , showStackItem 4 item . nl
            ]
        | (i, item) <- zip [1, 2 .. length stack] stack
        ]
    , strstr "--------------------------------" . nl
    ]

runTransition :: RuntimeEnv -> Stack -> [Stack] -> ExceptT KernelErr IO Satisfied
runTransition env = flip go where
    mkstrict :: (Context, [Cell]) -> (Context, [Cell])
    mkstrict (ctx, []) = ctx `seq` (ctx, [])
    mkstrict (ctx, cell : cells) = ctx `seq` cell `seq` (ctx, cell : cells)
    go :: [Stack] -> Stack -> ExceptT KernelErr IO Satisfied
    go [] [] = return False
    go (stack : stacks) [] = go stacks stack
    go stacks ((ctx, cells) : stack) = do
        liftIO (_PutStr env (showsCurrentState ctx cells stack ""))
        case cells of
            [] -> do
                want_more <- liftIO (_Answer env ctx)
                if want_more
                    then go stacks stack
                    else return True
            Cell facts level goal : cells' -> case unfoldlNApp (rewrite HNF goal) of
                (NCon (LO logical_operator), args) -> do
                    stack' <- runLogicalOperator logical_operator args ctx facts level cells' stack
                    go stacks stack'
                (NCon (DC pred), args) -> case makeConstraint pred args of
                    Nothing -> throwE (BadGoalGiven (foldlNApp (mkNCon (DC pred)) args))
                    Just constraint -> do
                        solutions <- _Reduce env facts (constraint : _LeftConstraints ctx) (_CurrentLabeling ctx)
                        go (stack : stacks)
                            [ mkstrict
                                ( Context (result_subst <> _TotalVarBinding ctx) new_labeling constraints
                                , concat
                                    [ [ Cell (applyBinding result_subst facts) level futher_goal | futher_goal <- futher_goals ]
                                    , [ Cell (applyBinding result_subst facts') level' (applyBinding result_subst goal') | Cell facts' level' goal' <- cells' ]
                                    ]
                                )
                            | Solution new_labeling result_subst constraints futher_goals <- solutions
                            ]
                (t, ts) -> throwE (BadGoalGiven (foldlNApp t ts))
