
-- | For graph-based DP algorithms we want to make a distinction between
-- edges and vertices. This modules defines a @Vertex@, a terminal symbol
-- that matches on individual vertices without reference to edges between
-- vertices.
--
-- TODO should be singleton-vertex ... rename!

module ADP.Fusion.Term.Vertex.Type where

import Data.Strict.Tuple

import Data.PrimitiveArray

import ADP.Fusion.Core.Classes
import ADP.Fusion.Core.Multi



-- | Returns the vertex in a graph.

data Vertex v where
  Vertex :: (Int -> v) -> Vertex v

instance Build (Vertex v)

instance
  ( Element ls i
  ) => Element (ls :!: Vertex v) i where
    data Elm (ls :!: Vertex v) i = ElmVertex !v !(RunningIndex i) (Elm ls i)
    type Arg (ls :!: Vertex v)   = Arg ls :. v
    getArg (ElmVertex v _ ls) = getArg ls :. v
    getIdx (ElmVertex _ i _ ) = i
    {-# Inline getArg #-}
    {-# Inline getIdx #-}

deriving instance (Show i, Show (RunningIndex i), Show v, Show (Elm ls i)) => Show (Elm (ls :!: Vertex v) i)

type instance TermArg (Vertex v) = v

