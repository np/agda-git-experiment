
module TypeChecking.Empty where

import Control.Applicative
import Control.Monad
import Control.Monad.State
import Control.Monad.Error

import Data.Map (Map)
import qualified Data.Map as Map

import Syntax.Common
import Syntax.Internal
import TypeChecking.Monad
import TypeChecking.Reduce
import TypeChecking.Errors
import TypeChecking.Primitive
import Utils.Function

-- | Make sure that a type is empty.
isEmptyType :: MonadTCM tcm => Type -> tcm ()
isEmptyType t = do
    t <- reduce t
    case t of
	El _ (Def d vs) -> do
	    Defn _ _ _ di <- getConstInfo d
	    case di of
		-- No constructors
		Datatype _ _ _ [] _ _ -> return ()

		-- Inductive family. Check that the type at the given index is
		-- uninhabited.
		Datatype nPs nIxs _ cs _ _ | nIxs > 0 -> do
		    ixs <- normalise $ map unArg vs
		    verbose 10 $ do
			ds <- mapM prettyTCM ixs
			liftIO $ putStrLn $ "empty inductive family?"
			liftIO $ putStrLn $ "nIxs = " ++ show nIxs
			liftIO $ print ds
		    mapM_ (impossibleConstr t ixs) cs

		-- Otherwise, it's not empty
		_ -> notEmpty t
	_ -> notEmpty t

notEmpty :: MonadTCM tcm => Type -> tcm a
notEmpty t = typeError $ ShouldBeEmpty t

-- | Make sure that a constructor cannot produce an element at the given index.
--   TODO: Handle cases like @zero == suc _@. To do this we need to do some
--   unification.
impossibleConstr :: MonadTCM tcm => Type -> [Term] -> QName -> tcm ()
impossibleConstr a ixs c = do
    reportLn 10 $ "impossible constructor " ++ show c ++ " ?"
    t <- normalise =<< typeOfConst c
    let Def _ vs = stripPi $ unEl t
	ixs'	 = map unArg vs
    d <- distinct ixs ixs'
    unless d $ notEmpty a
    where
	stripPi t = case t of
	    Pi _ b  -> stripPi $ unEl $ absBody b
	    Fun _ b -> stripPi $ unEl b
	    _	    -> t

-- | Make sure that two sequences of terms are distinct under any substitution.
--   The second sequence can contain variables.  Invariant: The terms should be
--   on normal form.
distinct :: MonadTCM tcm => [Term] -> [Term] -> tcm Bool
distinct us vs = do
    let go = zipWithM_ unify (map noVars us) (map yesVars vs)
    r <- liftTCM $ runErrorT $ evalStateT go Map.empty
    case r of
	Left err    -> return True
	Right _	    -> return False

type Substitution = Map Int Term

data UTerm = UTerm { hasVars :: Bool
		   , theTerm :: Term
		   }

noVars :: Term -> UTerm
noVars = UTerm False

yesVars :: Term -> UTerm
yesVars = UTerm True

instance Error () where
    noMsg    = ()
    strMsg _ = ()

-- | Unify two terms.  Successfull unification means that we couldn't find a
--   positive mismatch.
unify :: UTerm -> UTerm -> StateT Substitution (ErrorT () TCM) ()
unify u v = do
    s <- lift $ lift $ constructorForm $ theTerm u
    t <- lift $ lift $ constructorForm $ theTerm v
    let varsOf u t = (if hasVars u then yesVars else noVars) $ unArg t
    lift $ lift $ reportLn 10 $ "unifying " ++ hd s ++ " and " ++ hd t
    case (s, t) of
	(Con c us, Con c' vs)
	    | c /= c'	-> throwError ()
	    | otherwise	-> zipWithM_ unify (map (varsOf u) us)
					   (map (varsOf v) vs)
	(_, Var i []) | hasVars v   -> i =: s
	(Var i [], _) | hasVars u   -> i =: t
	_			    -> return ()
    where
	i =: t
	    | i `occursIn` t = throwError ()
	    | otherwise	     = do
		sub <- get
		case Map.lookup i sub of
		    Nothing -> put $ Map.insert i t sub
		    Just t' -> unify (noVars t) (noVars t')

	occursIn i (Con _ us) = any (occursIn i) $ map unArg us
	occursIn i (Var j []) = i == j
	occursIn _ _	      = False

	hd (Con c _)  = show c
	hd (Var i []) = show i
	hd _	      = "_"

