{-# OPTIONS -cpp #-}

module Agda.TypeChecking.Monad.Mutual where

import Control.Monad.Reader
import Control.Monad.State
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set

import Agda.Syntax.Internal
import Agda.TypeChecking.Monad.Base
import Agda.Utils.Fresh
import Agda.Utils.Impossible

#include "../../undefined.h"

inMutualBlock :: MonadTCM tcm => tcm a -> tcm a
inMutualBlock m = do
  mi <- asks envMutualBlock
  case mi of
    Nothing -> do
      i <- fresh
      flip local m $ \e -> e { envMutualBlock = Just i }
    -- Don't create a new mutual block if we're already inside one.
    Just _  -> m

-- | Set the mutual block for a definition
setMutualBlock :: MonadTCM tcm => MutualId -> QName -> tcm ()
setMutualBlock i x = do
  modify $ \s -> s { stMutualBlocks = Map.insertWith Set.union i (Set.singleton x) $ stMutualBlocks s
		   , stSignature    = (stSignature s)
				      { sigDefinitions = setMutId x i $ sigDefinitions $ stSignature s
				      }
		   }
  where
    setMutId x i = flip Map.adjust x $ \defn -> defn { defMutual = i }

-- | Get all mutual blocks
getMutualBlocks :: MonadTCM tcm => tcm [Set QName]
getMutualBlocks = gets $ Map.elems . stMutualBlocks

-- | Get the current mutual block.
currentMutualBlock :: MonadTCM tcm => tcm MutualId
currentMutualBlock = maybe fresh return =<< asks envMutualBlock

findMutualBlock :: MonadTCM tcm => QName -> tcm (Set QName)
findMutualBlock f = do
  bs <- getMutualBlocks
  case filter (Set.member f) bs of
    [b]   -> return b
    []    -> fail $ "No mutual block for " ++ show f
    _:_:_ -> __IMPOSSIBLE__

