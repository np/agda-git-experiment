{-# LANGUAGE CPP, Rank2Types #-}

-- | Generates data used for precise syntax highlighting.

module Agda.Interaction.Highlighting.Generate
  ( TypeCheckingState(..)
  , generateSyntaxInfo
  , generateErrorInfo
  , Agda.Interaction.Highlighting.Generate.tests
  )
  where

import Agda.Interaction.Highlighting.Precise hiding (tests)
import Agda.Interaction.Highlighting.Range   hiding (tests)
import Agda.TypeChecking.MetaVars (isBlockedTerm)
import Agda.TypeChecking.Monad
  hiding (MetaInfo, Primitive, Constructor, Record, Function, Datatype)
import qualified Agda.TypeChecking.Monad as M
import qualified Agda.TypeChecking.Reduce as R
import qualified Agda.Syntax.Abstract as A
import qualified Agda.Syntax.Concrete as C
import qualified Agda.Syntax.Internal as I
import qualified Agda.Syntax.Literal as L
import qualified Agda.Syntax.Parser as Pa
import qualified Agda.Syntax.Parser.Tokens as T
import qualified Agda.Syntax.Position as P
import qualified Agda.Syntax.Scope.Base as S
import qualified Agda.Syntax.Translation.ConcreteToAbstract as CA
import Agda.Utils.List
import Agda.Utils.TestHelpers
import Control.Monad
import Control.Monad.Trans
import Control.Monad.State
import Control.Applicative
import Data.Monoid
import Data.Generics
import Data.Function
import Agda.Utils.Generics
import Agda.Utils.FileName
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe
import Data.Sequence (Seq, (><))
import Data.List ((\\))
import qualified Data.Sequence as Seq
import qualified Data.Foldable as Fold (toList, fold, foldMap)

import Agda.Utils.Impossible
#include "../../undefined.h"

-- | Generates syntax highlighting information for an error,
-- represented as a range and a string. The range is first completed
-- so that there are no gaps in it.

generateErrorInfo :: P.Range -> String -> File
generateErrorInfo r s =
  several (rToR $ P.continuousPerLine r)
          (mempty { otherAspects = [Error], note = Just s })

-- | Has typechecking been done yet?

data TypeCheckingState = TypeCheckingDone | TypeCheckingNotDone
  deriving (Show, Eq)

-- | Generates syntax highlighting information.

generateSyntaxInfo
  :: FilePath               -- ^ The module to highlight.
  -> TypeCheckingState      -- ^ Has it been type checked?
  -> CA.TopLevelInfo        -- ^ The abstract syntax of the module.
  -> [([A.QName], [Range])] -- ^ Functions which failed to termination
                            --   check (grouped if they are mutual),
                            --   along with ranges for problematic
                            --   call sites.
  -> TCM HighlightingInfo
generateSyntaxInfo file tcs top termErrs =
  M.withScope_ (CA.insideScope top) $ M.ignoreAbstractMode $ do
    modMap <- sourceToModule file (CA.topLevelModuleName top)
    tokens <- liftIO $ Pa.parseFile' Pa.tokensParser file
    kinds  <- nameKinds tcs decls
    let nameInfo = mconcat $ map (generate modMap file kinds)
                                 (Fold.toList names)
    -- Constructors are only highlighted after type checking, since they
    -- can be overloaded.
    constructorInfo <-
      if tcs == TypeCheckingNotDone
         then return mempty
         else generateConstructorInfo modMap file kinds decls
    metaInfo <- if tcs == TypeCheckingNotDone
                   then return mempty
                   else computeUnsolvedMetaWarnings
    -- theRest needs to be placed before nameInfo here since record
    -- field declarations contain QNames. constructorInfo also needs
    -- to be placed before nameInfo since, when typechecking is done,
    -- constructors are included in both lists. Finally tokInfo is
    -- placed last since token highlighting is more crude than the
    -- others.
    return $ HighlightingInfo
               { source = file
               , info   = compress $
                            mconcat [ constructorInfo
                                    , theRest modMap
                                    , nameInfo
                                    , metaInfo
                                    , termInfo
                                    , tokInfo tokens
                                    ]
               }
  where
    decls = CA.topLevelDecls top

    tokInfo = Fold.foldMap tokenToFile
      where
      aToF a r = several (rToR r) (mempty { aspect = Just a })

      tokenToFile :: T.Token -> File
      tokenToFile (T.TokSetN (i, _))               = aToF PrimitiveType (P.getRange i)
      tokenToFile (T.TokKeyword T.KwSet  i)        = aToF PrimitiveType (P.getRange i)
      tokenToFile (T.TokKeyword T.KwProp i)        = aToF PrimitiveType (P.getRange i)
      tokenToFile (T.TokKeyword T.KwForall i)      = aToF Symbol (P.getRange i)
      tokenToFile (T.TokKeyword _ i)               = aToF Keyword (P.getRange i)
      tokenToFile (T.TokSymbol  _ i)               = aToF Symbol (P.getRange i)
      tokenToFile (T.TokLiteral (L.LitInt    r _)) = aToF Number r
      tokenToFile (T.TokLiteral (L.LitFloat  r _)) = aToF Number r
      tokenToFile (T.TokLiteral (L.LitString r _)) = aToF String r
      tokenToFile (T.TokLiteral (L.LitChar   r _)) = aToF String r
      tokenToFile (T.TokComment (i, _))            = aToF Comment (P.getRange i)
      tokenToFile (T.TokTeX (i, _))                = aToF Comment (P.getRange i)
      tokenToFile (T.TokId {})                     = mempty
      tokenToFile (T.TokQId {})                    = mempty
      tokenToFile (T.TokString {})                 = mempty
      tokenToFile (T.TokDummy {})                  = mempty
      tokenToFile (T.TokEOF {})                    = mempty

    termInfo = functionDefs `mappend` callSites
      where
      m            = mempty { otherAspects = [TerminationProblem] }
      functionDefs = Fold.foldMap (\x -> several (rToR $ bindingSite x) m) $
                     concatMap fst termErrs
      callSites    = Fold.foldMap (\r -> singleton r m) $
                     concatMap snd termErrs

    -- All names mentioned in the syntax tree (not bound variables).
    names = everything' (><) (Seq.empty `mkQ`  getName
                                        `extQ` getAmbiguous)
                        decls
      where
      getName :: A.QName -> Seq A.AmbiguousQName
      getName n = Seq.singleton (A.AmbQ [n])

      getAmbiguous :: A.AmbiguousQName -> Seq A.AmbiguousQName
      getAmbiguous = Seq.singleton

    -- Bound variables, dotted patterns, record fields and module
    -- names.
    theRest modMap = everything' mappend query decls
      where
      query :: GenericQ File
      query = mempty         `mkQ`
              getFieldDecl   `extQ`
              getVarAndField `extQ`
              getLet         `extQ`
              getLam         `extQ`
              getTyped       `extQ`
              getPattern     `extQ`
              getModuleName

      bound n = nameToFile modMap file []
                           (A.nameConcrete n)
                           (\isOp -> mempty { aspect = Just $ Name (Just Bound) isOp })
                           (Just $ A.nameBindingSite n)
      field m n = nameToFile modMap file m n
                             (\isOp -> mempty { aspect = Just $ Name (Just Field) isOp })
                             Nothing
      mod n = nameToFile modMap file []
                         (A.nameConcrete n)
                         (\isOp -> mempty { aspect = Just $ Name (Just Module) isOp })
                         (Just $ A.nameBindingSite n)

      getVarAndField :: A.Expr -> File
      getVarAndField (A.Var x)    = bound x
      getVarAndField (A.Rec _ fs) = mconcat $ map (field [] . fst) fs
      getVarAndField _            = mempty

      getLet :: A.LetBinding -> File
      getLet (A.LetBind _ x _ _) = bound x
      getLet A.LetApply{}        = mempty
      getLet A.LetOpen{}         = mempty

      getLam :: A.LamBinding -> File
      getLam (A.DomainFree _ x) = bound x
      getLam (A.DomainFull {})  = mempty

      getTyped :: A.TypedBinding -> File
      getTyped (A.TBind _ xs _) = mconcat $ map bound xs
      getTyped (A.TNoBind {})   = mempty

      getPattern :: A.Pattern -> File
      getPattern (A.VarP x)    = bound x
      getPattern (A.AsP _ x _) = bound x
      getPattern (A.DotP pi _) =
        several (rToR $ P.getRange pi)
                (mempty { otherAspects = [DottedPattern] })
      getPattern _             = mempty

      getFieldDecl :: A.Definition -> File
      getFieldDecl (A.RecDef _ _ _ _ fs) = Fold.foldMap extractField fs
        where
        extractField (A.ScopedDecl _ ds) = Fold.foldMap extractField ds
        extractField (A.Field _ x _)     = field (concreteQualifier x)
                                                 (concreteBase x)
        extractField _                   = mempty
      getFieldDecl _                   = mempty

      getModuleName :: A.ModuleName -> File
      getModuleName (A.MName { A.mnameToList = xs }) =
        mconcat $ map mod xs

-- | A function mapping names to the kind of name they stand for.

type NameKinds = A.QName -> Maybe NameKind

-- | Builds a 'NameKinds' function.

nameKinds :: TypeCheckingState
          -> [A.Declaration]
          -> TCM NameKinds
nameKinds tcs decls = do
  imported <- fix . stImports <$> get
  local    <- case tcs of
    TypeCheckingDone    -> fix . stSignature <$> get
    TypeCheckingNotDone -> return $
      -- Traverses the syntax tree and constructs a map from qualified
      -- names to name kinds. TODO: Handle open public.
      everything' union (Map.empty `mkQ` getDef `extQ` getDecl) decls
  let merged = Map.union local imported
  return (\n -> Map.lookup n merged)
  where
  fix = Map.map (defnToNameKind . theDef) . sigDefinitions

  -- | The 'M.Axiom' constructor is used to represent various things
  -- which are not really axioms, so when maps are merged 'Postulate's
  -- are thrown away whenever possible. The 'getDef' and 'getDecl'
  -- functions below can return several explanations for one qualified
  -- name; the 'Postulate's are bogus.
  union = Map.unionWith dropPostulates
    where
    dropPostulates Postulate k = k
    dropPostulates k         _ = k

  defnToNameKind :: Defn -> NameKind
  defnToNameKind (M.Axiom {})                     = Postulate
  defnToNameKind (M.Function {})                  = Function
  defnToNameKind (M.Datatype {})                  = Datatype
  defnToNameKind (M.Record {})                    = Record
  defnToNameKind (M.Constructor { M.conInd = i }) = Constructor i
  defnToNameKind (M.Primitive {})                 = Primitive

  getAxiomName :: A.Declaration -> A.QName
  getAxiomName (A.Axiom _ q _) = q
  getAxiomName _               = __IMPOSSIBLE__

  getDef :: A.Definition -> Map A.QName NameKind
  getDef (A.FunDef  _ q _)      = Map.singleton q Function
  getDef (A.DataDef _ q i _ cs) = Map.singleton q Datatype `union`
                                  (Map.unions $
                                   map (\q -> Map.singleton q (Constructor i)) $
                                   map getAxiomName cs)
  getDef (A.RecDef  _ q _ _ _)  = Map.singleton q Record
  getDef (A.ScopedDef {})       = Map.empty

  getDecl :: A.Declaration -> Map A.QName NameKind
  getDecl (A.Axiom _ q _)     = Map.singleton q Postulate
  getDecl (A.Field _ q _)     = Map.singleton q Field
  getDecl (A.Primitive _ q _) = Map.singleton q Primitive
  getDecl (A.Definition {})   = Map.empty
  getDecl (A.Section {})      = Map.empty
  getDecl (A.Apply {})        = Map.empty
  getDecl (A.Import {})       = Map.empty
  getDecl (A.Pragma {})       = Map.empty
  getDecl (A.ScopedDecl {})   = Map.empty
  getDecl (A.Open {})         = Map.empty

-- | Generates syntax highlighting information for all constructors
-- occurring in patterns and expressions in the given declarations.
--
-- This function should only be called after type checking.
-- Constructors can be overloaded, and the overloading is resolved by
-- the type checker.

generateConstructorInfo
  :: SourceToModule  -- ^ Maps source file paths to module names.
  -> FilePath        -- ^ The module to highlight.
  -> NameKinds
  -> [A.Declaration]
  -> TCM File
generateConstructorInfo modMap file kinds decls = do
  -- Extract all defined names from the declaration list.
  let names = Fold.toList $ Fold.foldMap A.allNames decls

  -- Look up the corresponding declarations in the internal syntax.
  defMap <- M.sigDefinitions <$> M.getSignature
  let defs = catMaybes $ map (flip Map.lookup defMap) names

  -- Instantiate meta variables.
  clauses <- R.instantiateFull $ concatMap M.defClauses defs
  types   <- R.instantiateFull $ map defType defs

  -- Find all constructors occurring in type signatures or clauses
  -- within the given declarations.
  constrs <- everything' (liftM2 (><)) query (types, clauses)

  -- Return suitable syntax highlighting information.
  return $ Fold.fold $ fmap (generate modMap file kinds . mkAmb) constrs
  where
  mkAmb q = A.AmbQ [q]

  query :: GenericQ (TCM (Seq A.QName))
  query = return mempty   `mkQ`
          getConstructor  `extQ`
          getConstructorP

  getConstructor :: I.Term -> TCM (Seq A.QName)
  getConstructor (I.Con q _) = return $ Seq.singleton q
  getConstructor (I.Def c _) = retrieveCoconstructor c
  getConstructor _           = return Seq.empty

  getConstructorP :: I.Pattern -> TCM (Seq A.QName)
  getConstructorP (I.ConP q _) = return $ Seq.singleton q
  getConstructorP _            = return Seq.empty

  retrieveCoconstructor :: A.QName -> TCM (Seq A.QName)
  retrieveCoconstructor c = do
    def <- getConstInfo c
    case defDelayed def of
      NotDelayed -> return Seq.empty  -- not a coconstructor
      Delayed -> case defClauses def of
        [I.Clause{ I.clauseBody = body}] -> case getRHS body of
          Just (I.Con c _) -> return $ Seq.singleton c
          _                -> return Seq.empty
        _ -> return Seq.empty
    where
      getRHS (I.Body v)   = Just v
      getRHS I.NoBody     = Nothing
      getRHS (I.Bind b)   = getRHS (I.absBody b)
      getRHS (I.NoBind b) = getRHS b

-- | Generates syntax highlighting information for unsolved meta
-- variables.

computeUnsolvedMetaWarnings :: TCM File
computeUnsolvedMetaWarnings = do
  is <- getInteractionMetas

  -- We don't want to highlight blocked terms, since
  --   * there is always at least one proper meta responsible for the blocking
  --   * in many cases the blocked term covers the highlighting for this meta
  let notBlocked m = not <$> isBlockedTerm m
  ms <- filterM notBlocked =<< getOpenMetas

  rs <- mapM getMetaRange (ms \\ is)
  return $ several (concatMap (rToR . P.continuousPerLine) rs)
         $ mempty { otherAspects = [UnsolvedMeta] }

-- | Generates a suitable file for a possibly ambiguous name.

generate :: SourceToModule
            -- ^ Maps source file paths to module names.
         -> FilePath
            -- ^ The module to highlight.
         -> NameKinds
         -> A.AmbiguousQName
         -> File
generate modMap file kinds (A.AmbQ qs) =
  mconcat $ map (\q -> nameToFileA modMap file q include m) qs
  where
    ks   = map kinds qs
    kind = case (allEqual ks, ks) of
             (True, Just k : _) -> Just k
             _                  -> Nothing
    -- Note that all names in an AmbiguousQName should have the same
    -- concrete name, so either they are all operators, or none of
    -- them are.
    m isOp  = mempty { aspect = Just $ Name kind isOp }
    include = allEqual (map bindingSite qs)

-- | Converts names to suitable 'File's.

nameToFile :: SourceToModule
              -- ^ Maps source file paths to module names.
           -> FilePath
              -- ^ The file name of the current module. Used for
              -- consistency checking.
           -> [C.Name]
              -- ^ The name qualifier (may be empty).
           -> C.Name
              -- ^ The base name.
           -> (Bool -> MetaInfo)
              -- ^ Meta information to be associated with the name.
              -- The argument is 'True' iff the name is an operator.
           -> Maybe P.Range
              -- ^ The definition site of the name. The calculated
              -- meta information is extended with this information,
              -- if possible.
           -> File
nameToFile modMap file xs x m mR =
  -- Make sure that we don't get any funny ranges.
  if all (== file) $ catMaybes $
     map (fmap P.srcFile . P.rStart . P.getRange) (x : xs) then
    several rs' ((m isOp) { definitionSite = mFilePos })
   else
    __IMPOSSIBLE__
  where
  (rs, isOp) = getRanges x
  rs'        = rs ++ concatMap (fst . getRanges) xs
  mFilePos   = do
    r <- mR
    P.Pn { P.srcFile = f, P.posPos = p } <- P.rStart r
    mod <- Map.lookup f modMap
    return (toStrings mod, f, toInteger p)

-- | A variant of 'nameToFile' for qualified abstract names.

nameToFileA :: SourceToModule
               -- ^ Maps source file paths to module names.
            -> FilePath
               -- ^ The file name of the current module. Used for
               -- consistency checking.
            -> A.QName
               -- ^ The name.
            -> Bool
               -- ^ Should the binding site be included in the file?
            -> (Bool -> MetaInfo)
               -- ^ Meta information to be associated with the name.
               -- ^ The argument is 'True' iff the name is an operator.
            -> File
nameToFileA modMap file x include m =
  nameToFile modMap
             file
             (concreteQualifier x)
             (concreteBase x)
             m
             (if include then Just $ bindingSite x else Nothing)

concreteBase      = A.nameConcrete . A.qnameName
concreteQualifier = map A.nameConcrete . A.mnameToList . A.qnameModule
bindingSite       = A.nameBindingSite . A.qnameName
toStrings         = map show . A.mnameToList

-- | Maps source file names to the corresponding top-level module
-- names.

type SourceToModule = Map FilePath A.ModuleName

sourceToModule
  :: FilePath            -- ^ The current source file.
  -> A.ModuleName        -- ^ The current top-level module name.
  -> TCM SourceToModule
sourceToModule file mod =
  Map.fromList .
  (:) (file, mod) .
  map (\(m, (i, _)) -> (source $ M.iHighlighting i, m)) .
  Map.toList <$>
  M.getVisitedModules

-- | Like 'everything', but modified so that it does not descend into
-- everything.

everything' :: (r -> r -> r) -> GenericQ r -> GenericQ r
everything' (+) = everythingBut
                    (+)
                    (False `mkQ` isString
                           `extQ` isAQName `extQ` isAName `extQ` isCName
                           `extQ` isScope `extQ` isMap1 `extQ` isMap2
                           `extQ` isAmbiguous)
  where
  isString    :: String                        -> Bool
  isAQName    :: A.QName                       -> Bool
  isAName     :: A.Name                        -> Bool
  isCName     :: C.Name                        -> Bool
  isScope     :: S.ScopeInfo                   -> Bool
  isMap1      :: Map A.QName A.QName           -> Bool
  isMap2      :: Map A.ModuleName A.ModuleName -> Bool
  isAmbiguous :: A.AmbiguousQName              -> Bool

  isString    = const True
  isAQName    = const True
  isAName     = const True
  isCName     = const True
  isScope     = const True
  isMap1      = const True
  isMap2      = const True
  isAmbiguous = const True

------------------------------------------------------------------------
-- All tests

-- | All the properties.

tests :: IO Bool
tests = runTests "Agda.Interaction.Highlighting.Generate" []
