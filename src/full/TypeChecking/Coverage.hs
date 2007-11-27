{-# OPTIONS -cpp #-}

module TypeChecking.Coverage where

import Control.Monad

import Syntax.Common
import Syntax.Internal
import Syntax.Internal.Pattern
import TypeChecking.Monad.Base
import TypeChecking.Monad.Signature
import TypeChecking.Monad.Options
import TypeChecking.Pretty
import TypeChecking.Substitute
import Utils.Permutation
import Utils.Size

#include "../undefined.h"

data SplitClause = SClause
      { scTel   :: Telescope      -- ^ type of variables in scPats
      , scPerm  :: Permutation    -- ^ how to get from the variables in the patterns to the telescope
      , scPats  :: [Arg Pattern]
      , scSubst :: [Term]         -- ^ substitution from scTel to old context
      }

type Covering = [SplitClause]

typeOfVar :: Telescope -> Nat -> Type
typeOfVar tel n
  | n >= len  = __IMPOSSIBLE__
  | otherwise = raise (n + 1) . snd . unArg $ ts !! n
  where
    len = length ts
    ts  = reverse $ telToList tel

checkCoverage :: QName -> TCM ()
checkCoverage f = do
  d <- getConstInfo f
  let t    = defType d
      defn = theDef d
  case defn of
    Function cs _ -> mapM_ splitC cs
    _             -> __IMPOSSIBLE__
  where
    splitClause cl@(Clause tel _ _ _) = mapM_ (\i -> splitClause cl i) [0..size tel - 1]

-- | split Δ x ps. Δ ⊢ ps, x ∈ Δ (deBruijn index)
splitClause :: Clause -> Nat -> TCM Covering
splitClause (Clause tel perm ps _) x = do
  reportSDoc "tc.cover.top" 10 $ vcat
    [ text "split"
    , nest 2 $ vcat
      [ text "tel  =" <+> prettyTCM tel
      , text "perm =" <+> text (show perm)
      , text "x    =" <+> text (show x)
      , text "ps   =" <+> text (show ps)
      ]
    ]

  let t     = typeOfVar tel x   -- what context should this be in?
      holes = reverse $ permute perm $ allHolesWithContents ps

  unless (length holes == length (telToList tel)) $
    fail "split: bad holes or tel"

  -- There is always a variable at the given hole.
  let (VarP s, hps) = holes !! x

  reportSDoc "tc.cover.top" 10 $ nest 2 $ vcat $
    [ text "p   =" <+> text s
    , text "hps =" <+> text (show hps)
    , text "t   =" <+> prettyTCM t
    ]

  let same = SClause tel perm ps (idSub tel)

  return [same, same]

