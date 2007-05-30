{-# OPTIONS -fglasgow-exts -cpp #-}

#include "../../undefined.h"

{-| main module.
-}

module Compiler.Agate.Main where

import Compiler.Agate.TranslateName
import Compiler.Agate.OptimizedPrinter
import Compiler.Agate.UntypedPrinter
import Compiler.Agate.Common

import Syntax.Internal
import Text.PrettyPrint
import Syntax.Common

import Control.Monad.State
import Control.Monad.Error

import Data.List as List
import qualified Data.Map as Map
import Data.Map (Map)

import Syntax.Abstract.Name

import Interaction.Options
import Interaction.Monad

import TypeChecker
import TypeChecking.Monad
import TypeChecking.Reduce

import Utils.Monad

import Version

-- | The main function
compilerMain :: IM () -> IM ()
compilerMain typeCheck = do
	typeCheck
	sig <- gets stSignature
	let definitions = sigDefinitions sig
	let defs = Map.toList definitions
	maxconargs <- computeMaxArity definitions
	liftIO $ do
	    putStrLn "{-# OPTIONS -fglasgow-exts -cpp #-}"
	    putStrLn ""
	    putStrLn "-- Generated by Agate 2"
	    putStrLn ""
	    printConstants definitions
	    putStrLn ""
	    putStrLn "data Value = VAbs (Value -> Value)"
	    putStrLn "           | VCon0 !Int"
	    mapM_ (\k -> putStrLn $ "           | VCon" ++ show k ++ " !Int"
	 			 ++ concat (replicate k " Value") )
	    	  [1..maxconargs]
	    putStrLn "           | VNonData"
	    putStrLn "           | VIO      !(IO Value)"
	    putStrLn "           | VInt     !Integer"
	    putStrLn "           | VFloat   !Double"
	    putStrLn "           | VString  !String"
	    putStrLn "           | VChar    !Char"
	    putStrLn ""
	    putStrLn "instance Show Value where"
	    putStrLn "  show v = case v of"
	    putStrLn "    VAbs     f     -> \"<func>\""
	    putStrLn "    VCon0    c     -> getConString c"
	    mapM_ (\k -> putStrLn $ "    VCon" ++ show k ++ "    c"
	 			 ++ concatMap (\i -> " a" ++ show i) [1..k]
	 			 ++ "\t-> showCons c [a1"
	 			 ++ concatMap (\i -> ",a" ++ show i) [2..k]
	 			 ++ "]" )
	    	  [1..maxconargs]
	    putStrLn "    VNonData       -> \"<nondata>\""
	    putStrLn "    VIO      m     -> \"<IO>\""
	    putStrLn "    VInt     i     -> show i"
	    putStrLn "    VFloat   f     -> show f"
	    putStrLn "    VString  s     -> show s"
	    putStrLn "    VChar    c     -> show c"
	    putStrLn ""
	    --putStrLn "join sep []     = \"\""
	    --putStrLn "join sep [a]    = a"
	    --putStrLn "join sep (a:as) = a ++ sep ++ join sep as"
	    putStrLn ""
	    putStrLn "showCons c as = \"(\" ++ unwords (getConString c : map show as) ++ \")\""
	    putStrLn "showBind (f,v) = show v"
	    putStrLn ""
	    printShowConstants definitions
	    putStrLn "getConString c = show c"
	    putStrLn ""
    	    putStrLn "(|$|) :: Value -> Value -> Value"
	    putStrLn "(VAbs f) |$| x = f x"
	    putStrLn ""
	    putStrLn "class Trans a where"
	    putStrLn "    unbox :: Value -> a"
	    putStrLn "    box   :: a -> Value"
	    putStrLn ""
	    putStrLn "instance Trans () where"
	    putStrLn "    unbox VNonData = ()"
	    putStrLn "    box () = VNonData"
	    putStrLn ""
	    putStrLn "instance (Trans a, Trans b) => Trans (a -> b) where"
	    putStrLn "    unbox (VAbs f) = unbox . f . box"
	    putStrLn "    box f = VAbs ( box . f . unbox )"
	    putStrLn ""
	    putStrLn "instance Trans Integer where"
	    putStrLn "    unbox (VInt i) = i"
	    putStrLn "    box i = VInt i"
	    putStrLn ""
	    putStrLn "instance Trans Double where"
	    putStrLn "    unbox (VFloat f) = f"
	    putStrLn "    box f = VFloat f"
	    putStrLn ""
	    putStrLn "instance Trans String where"
	    putStrLn "    unbox (VString s) = s"
	    putStrLn "    box s = VString s"
	    putStrLn ""
	    putStrLn "instance Trans Char where"
	    putStrLn "    unbox (VChar c) = c"
	    putStrLn "    box c = VChar c"
	    putStrLn ""
	    putStrLn "main = putStrLn $ show x_Main__main"
	liftIO $ putStrLn $ "--"
	ddefs <- mapM showUntypedDefinition defs
	liftIO $ putStrLn $ render $ vcat ddefs
	showOptimizedDefinitions definitions

enumConstructors :: Definitions -> [QName]
enumConstructors = concatMap f . Map.toList where
    f (name, d) = case theDef d of
			Constructor _ _ _ _ -> [name]
                        Record  _ _ _ _ _ _ -> [name]
                        _                   -> []

computeMaxArity :: Definitions -> IM Int
computeMaxArity dd =
    fmap maximum $ mapM getConstructorArity $ map snd $ Map.toList dd

getConstructorArity :: Definition -> IM Int
getConstructorArity defn = case theDef defn of
    Record np clauses flds tel s a -> return $ length flds
    Constructor np _ qtname a -> do
	ty <- normalise $ defType defn
	(args,_) <- splitType ty
	return $ length args - np
    _ -> return 0

printConstants :: Definitions -> IO ()
printConstants dd = mapM_ go $ zip (enumConstructors dd) [1..] where
    go (name,n) = let cname = translateNameAsUntypedConstructor $ show name in
		  putStrLn $ "#define " ++ cname ++ " " ++ show n

printShowConstants :: Definitions -> IO ()
printShowConstants dd = mapM_ go $ zip (enumConstructors dd) [1..] where
    go (name,n) = let pname = show $ qnameName name in
		  putStrLn $ "getConString " ++ show n ++ " = \"" ++ pname ++ "\""

----------------------------------------------------------------
