
-- |
--
-- TODO merge with @Edge@ and handle via phantom typing?

module ADP.Fusion.Term.EdgeWithSet.Type where

import Data.Strict.Tuple

import Data.PrimitiveArray

import ADP.Fusion.Core.Classes
import ADP.Fusion.Core.Multi
import ADP.Fusion.Term.Edge.Type (From(..), To(..))



-- | An edge in a graph. As a parsing symbol, it will provide (From:.To)
-- pairs.

data EdgeWithSet = EdgeWithSet

instance Build EdgeWithSet

instance
  ( Element ls i
  ) => Element (ls :!: EdgeWithSet) i where
    data Elm (ls :!: EdgeWithSet) i = ElmEdgeWithSet !(Int:.From:.To) !(RunningIndex i) (Elm ls i)
    type Arg (ls :!: EdgeWithSet)   = Arg ls :. (Int:.From:.To)
    getArg (ElmEdgeWithSet e _ ls) = getArg ls :. e
    getIdx (ElmEdgeWithSet _ i _ ) = i
    {-# Inline getArg #-}
    {-# Inline getIdx #-}

deriving instance (Show i, Show (RunningIndex i), Show (Elm ls i)) => Show (Elm (ls :!: EdgeWithSet) i)

type instance TermArg EdgeWithSet = (Int:.From:.To)

