
module ADP.Fusion.Term.Edge.Set2 where

import Data.Bits
import Data.Strict.Tuple
import Data.Vector.Fusion.Stream.Monadic hiding (flatten)
import Debug.Trace
import Prelude hiding (map)

import ADP.Fusion.Core
import Data.Bits.Ordered
import Data.PrimitiveArray hiding (map)

import ADP.Fusion.Core.Set
import ADP.Fusion.Term.Edge.Type



instance
  ( TmkCtx1 m ls (Edge e) (BS2 First Last i)
  ) => MkStream m (ls :!: Edge e) (BS2 First Last i) where
  mkStream (ls :!: Edge f) sv us is
    = map (\(ss,ee,ii) -> ElmEdge ee ii ss)
    . addTermStream1 (Edge f) sv us is
    $ mkStream ls (termStaticVar (Edge f) sv is) us (termStreamIndex (Edge f) sv is)
  {-# Inline mkStream #-}

{-
-- | Introduce a singleton vertex into an empty set structure, where the
-- set structure has explicitly annotaed first and last set vertices. This
-- means that first and last point to the same element.

instance
  ( TstCtx m ts s x0 i0 is (BS2 First Last I)
  ) => TermStream m (TermSymbol ts (Singleton v)) s (is:.BS2 First Last I) where
  -- If we are static, we need to check that we will flip the first bit.
  termStream (ts:|Singleton f) (cs:.IStatic d) (us:.BS2 ss ui uj) (is:.BS2 s i j)
    = map go . termStream ts cs us is . staticCheck (popCount s == 1 && d == 0)
    where go (TState zz ii ee) = TState zz (ii:.:RiBs2I (BS2 s i j)) (ee:.f (getIter i))
  termStream (ts:|Singleton f) (cs:.IVariable d) (us:.BS2 ss ui uj) (is:.BS2 s i j)
    = map go . termStream ts cs us is . staticCheck (popCount s == 1 && d == 0)
    where go (TState zz ii ee) = TState zz (ii:.:RiBs2I (BS2 s i j)) (ee:.f (getIter i))
  {-# Inline termStream #-}
-}

instance TermStaticVar (Edge e) (BS2 First Last I) where
  termStaticVar   _ (IStatic   d) _ = IStatic   $ d+1
  termStaticVar   _ (IVariable d) _ = IVariable $ d+1
  termStreamIndex _ _  ix = ix
  {-# Inline [0] termStaticVar #-}
  {-# Inline [0] termStreamIndex #-}

