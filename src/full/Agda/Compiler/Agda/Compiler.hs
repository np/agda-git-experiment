{-# LANGUAGE CPP #-}

module Agda.Compiler.Agda.Compiler where

import Prelude hiding ( null, writeFile )
import Control.Monad.Reader ( liftIO )
import Control.Monad.State ( get, put )
import Data.List ( intercalate, map, filter, isPrefixOf, concat, genericDrop, genericLength, partition )
import Data.Set ( Set, empty, null, insert, difference, delete )
import Data.Map ( Map, fold, singleton, fromList, toList, toAscList, insertWith, elems )
import qualified Data.Set as Set
import qualified Data.Map as Map
import System.Directory ( createDirectoryIfMissing )
import System.FilePath ( pathSeparator, splitFileName, (</>), (<.>) )

import Agda.Interaction.FindFile ( findFile, findInterfaceFile )
import Agda.Interaction.Imports ( isNewerThan )
import Agda.Interaction.Options ( optCompileDir )
import Agda.Syntax.Common ( Nat, Arg, unArg, Relevance(Relevant), defaultArgInfo )
import Agda.Syntax.Concrete.Name ( projectRoot )
import Agda.Syntax.Abstract.Name
  ( ModuleName(MName), QName(QName), QNamed(QNamed),
    mnameToList, mnameFromList, freshName_, qualifyM,
    qnameName, qnameModule, isInModule, nameId )
import Agda.Syntax.Internal
  ( Name, Args, Type,
    Clause(Clause), Pattern(VarP,DotP,LitP,ConP), Abs(Abs),
    ClauseBody(Body,NoBody,Bind),
    Term(Var,Lam,Lit,Level,Def,Con,Pi,Sort,MetaV,DontCare,Shared),
    derefPtr,
    toTopLevelModuleName, clausePats, clauseBody, arity, unEl, unAbs )
import Agda.TypeChecking.Substitute ( absBody )
import Agda.Syntax.Literal ( Literal(LitInt,LitFloat,LitString,LitChar,LitQName) )
import Agda.TypeChecking.Level ( reallyUnLevelView )
import Agda.TypeChecking.Monad
  ( TCM, Definition(Defn), Definitions, Interface,
    JSCode, Defn(Record,Datatype,Constructor,Primitive,Function,Axiom),
    iModuleName, iImportedModules, theDef, getConstInfo, typeOfConst,
    ignoreAbstractMode, miInterface, getVisitedModules,
    defName, defType, funClauses, funProjection,
    dataPars, dataIxs, dataClause, dataCons,
    conPars, conData, conSrcCon,
    recClause, recCon, recFields, recPars, recNamedCon,
    primClauses, defJSDef )
import Agda.TypeChecking.Monad.Options ( setCommandLineOptions, commandLineOptions, reportSLn )
import Agda.TypeChecking.Reduce ( instantiateFull, normalise )
import Agda.Utils.FileName ( filePath )
import Agda.Utils.Function ( iterate' )
import Agda.Utils.Monad ( (<$>), (<*>), localState, ifM )
import Agda.Utils.IO.UTF8 ( writeFile )
import Agda.Utils.Impossible ( Impossible(Impossible), throwImpossible )
import qualified Agda.Utils.HashMap as HMap
import Agda.Compiler.MAlonzo.Misc ( curDefs, curIF, curMName, setInterface )
import Agda.Compiler.MAlonzo.Primitives ( repl )

import qualified Agda.Syntax.Concrete as C
--import qualified Agda.Syntax.Abstract as A
import Control.Monad ( (<=<) )
import qualified Agda.Utils.Pretty as P
import Agda.TypeChecking.Pretty
--import Agda.Syntax.Concrete.Pretty
import Agda.Syntax.Translation.InternalToAbstract
import Agda.Syntax.Translation.AbstractToConcrete

#include "../../undefined.h"

-- TODO share this with JS
-- make the JS compiler use this

compileDir :: TCM FilePath
compileDir = do
  mdir <- optCompileDir <$> commandLineOptions
  case mdir of
    Just dir -> return dir
    Nothing  -> __IMPOSSIBLE__

data Compiler = Compiler
  { compileModuleName :: ModuleName -> TCM FilePath
  , compileCurModule  :: TCM String
  }

compilerMain' :: Compiler -> Interface -> TCM ()
compilerMain' c mainI =
  -- Preserve the state (the compiler modifies the state).
  localState $ do
    computeOutputDirectory
    ignoreAbstractMode $ do
      mapM_ (compile . miInterface) =<< (elems <$> getVisitedModules)

  where

  -- Compute the output directory.
  computeOutputDirectory :: TCM ()
  computeOutputDirectory = do
    opts <- commandLineOptions
    compileDir <- case optCompileDir opts of
      Just dir -> return dir
      Nothing  -> do
        -- The default output directory is the project root.
        let tm = toTopLevelModuleName $ iModuleName mainI
        f <- findFile tm
        return $ filePath $ projectRoot f tm
    setCommandLineOptions $
      opts { optCompileDir = Just compileDir }

  compile :: Interface -> TCM ()
  compile i = do
    setInterface i
    ifM uptodate noComp $ (yesComp >>) $ do
      m <- curMName
      mbody <- compileCurModule c
      out <- outFile m
      liftIO (writeFile out mbody)

  outFile :: ModuleName -> TCM FilePath
  outFile m = do
    mdir <- compileDir
    cfp  <- compileModuleName c m
    let (fdir, fn) = splitFileName cfp
    let dir = mdir </> fdir
        fp  = dir </> fn
    liftIO $ createDirectoryIfMissing True dir
    return fp

  outFile_ = outFile =<< curMName
  uptodate = liftIO =<< (isNewerThan <$> outFile_ <*> ifile)
  ifile    = maybe __IMPOSSIBLE__ filePath <$>
               (findInterfaceFile . toTopLevelModuleName =<< curMName)
  noComp   = reportSLn "" 1 . (++ " : no compilation is needed.").show =<< curMName
  yesComp  = reportSLn "" 1 . (`repl` "Compiling <<0>> in <<1>> to <<2>>") =<<
             sequence [show <$> curMName, ifile, outFile_] :: TCM ()

-- Each time the compiler is initialized the root module name will
-- get a different id.
initializeCompiler :: TCM Compiler
initializeCompiler = do
  prefix <- mnameFromList . (:[]) <$> freshName_ "AgdaAgda"
  let agdaMod :: ModuleName -> TCM FilePath
      agdaMod = return . (<.> ".agda") . foldl1 (</>) . map show . mnameToList . qualifyM prefix
  return $ Compiler agdaMod (curModule prefix)

compilerMain :: Interface -> TCM ()
compilerMain i = do c <- initializeCompiler
                    compilerMain' c i

curModule :: ModuleName -> TCM String
curModule prefix = do
  let aaMod = qualifyM prefix
  m <- aaMod <$> curMName
  is <- map aaMod <$> (iImportedModules <$> curIF)
  es <- mapM definition =<< (HMap.toList <$> curDefs)
  -- TODO print module header
  return (show (P.vcat es)) -- (Module m ({-reorder-} es))

definition :: (QName,Definition) -> TCM Doc
definition (q,d) = do
  -- (_,ls) <- global q
  -- d <- instantiateFull d
  e <- defn q (defType d) (theDef d)
  return e -- (Export ls e)

typeSig :: QName -> Type -> TCM Doc
typeSig q t = sep [ prettyA q <+> text ":" , nest 2 $ prettyI t ]

defn :: QName -> Type -> Defn -> TCM Doc -- Exp
defn q t (Function { funProjection = Nothing, funClauses = cls }) = do
  sig <- typeSig q t
  cs <- mapM (prettyI . QNamed q) cls
  return $ P.vcat (sig : cs)
defn _ _ _ = return $ P.text "-- TODO"

prettyI :: (Reify i a, ToConcrete a c, P.Pretty c) => i -> TCM Doc
prettyI = prettyA <=< reify
