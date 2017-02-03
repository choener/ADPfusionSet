
-- | Insert an edge into a set. @X -> Y e@ with @e == Edge@ extends @Y@
-- with the edge partially overlapping @Y@.
--
-- The semantic meaning of the overlap depends on what the @k@ type in @BS1
-- k i@ is. For @First@, the edge will go from @First@ in @X@ to @First@ in
-- the smaller @Y@.
--
-- TODO @X -> e X@ vs @X -> X e@.
--
-- Sidenote: can we actually have @X -> Y Z@ with @Set1@ structures?
-- I don't think so, at least not easily, since the boundary between @Y Z@
-- is unclear.

module ADP.Fusion.Term.Edge.Set1 where

import Data.Bits
import Data.Strict.Tuple
import Data.Vector.Fusion.Stream.Monadic hiding (flatten)
import Debug.Trace
import Prelude hiding (map)

import ADP.Fusion.Core
import Data.Bits.Ordered
import Data.PrimitiveArray hiding (map)

import ADP.Fusion.Core.Set1
import ADP.Fusion.Term.Edge.Type



instance
  ( TmkCtx1 m ls (Edge e) (BS1 k t)
  ) => MkStream m (ls :!: Edge e) (BS1 k t) where
  mkStream (ls :!: Edge f) sv us is
    = map (\(ss,ee,ii) -> ElmEdge ee ii ss)
    . addTermStream1 (Edge f) sv us is
    $ mkStream ls (termStaticVar (Edge f) sv is) us (termStreamIndex (Edge f) sv is)
  {-# Inline mkStream #-}

-- | We need to separate out the two cases of having @BS1 First@ and @BS1
-- Last@ as this changes how we fill the Edge.
--
-- TODO separate out these cases into an Edge-Choice class ...

instance
  ( TstCtx m ts s x0 i0 is (BS1 k I)
  ) => TermStream m (TermSymbol ts (Edge v)) s (is:.BS1 k I) where
  -- Begin the edge on @First == b@, and end it somewhere in the set.
  termStream (ts:|edge) (cs:.IStatic r) (us:.u) (is:.BS1 i (Boundary newNode))
    = map (\(TState s ii ee) ->
        let RiBs1I (BS1 cset (Boundary setNode)) = getIndex (getIdx s) (Proxy :: PRI is (BS1 k I))
        in  TState s (ii:.:RiBs1I (BS1 i (Boundary newNode)))
                     (ee:.edgeFromTo (Proxy :: Proxy First) edge (SetNode setNode) (NewNode newNode)) )
    . termStream ts cs us is
  -- Begin the edge somewhere, because in the variable case we do not end
  -- on @b@
  termStream (ts:|edge) (cs:.IVariable r) (us:.u) (is:.BS1 i b)
    = flatten mk step . termStream ts cs us is
          -- get us the inner set, build an edge @avail -> to@
    where mk tstate@(TState s ii ee) =
            let RiBs1I (BS1 cset (Boundary setNode)) = getIndex (getIdx s) (Proxy :: PRI is (BS1 k I))
                avail = activeBitsL $ (i .&. complement cset) `clearBit` getBoundary b
            in  return $ (tstate,cset,setNode,avail)
          -- in @X -> Y e Z@, @e == Edge@ will only be active, if @Y@ has
          -- at least one active bit. This means that @X -> e ...@ will
          -- never be active.
          step (_,_,_,[]) = return $ Done
          step (TState s ii ee,cset,setNode,(newNode:xs))
            | setNode < 0  = error "Edge/Set1: source boundary is '-1'. Move all terminals to the right of syntactic variables!"
            | otherwise =
              let ix = RiBs1I $ BS1 (cset `setBit` newNode) (Boundary newNode)
              in  return $ Yield (TState s (ii:.:ix) (ee:.edgeFromTo (Proxy :: Proxy First) edge (SetNode setNode) (NewNode newNode)))
                                 (TState s ii ee,cset,setNode,xs)
          {-# Inline [0] mk   #-}
          {-# Inline [0] step #-}
  {-# Inline termStream #-}

-- |
--
-- TODO move to definition of 'Edge'

class EdgeFromTo k where
  edgeFromTo :: forall e . Proxy k -> Edge e -> SetNode -> NewNode -> e

newtype SetNode = SetNode Int

newtype NewNode = NewNode Int

-- | In case our sets have a @First@ boundary, then we always point from
-- the boundary "into" the set. Hence @SetNode == To@ and @NewNode ==
-- From@.

instance EdgeFromTo First where
  edgeFromTo Proxy (Edge f) (SetNode to) (NewNode from) = f (From from) (To to)
  {-# Inline edgeFromTo #-}

-- | And if the set has a @Last@ boundary, then we point from somewhere in
-- the set @To@ the @NewNode@, which is @Last@.

instance EdgeFromTo Last where
  edgeFromTo Proxy (Edge f) (SetNode from) (NewNode to) = f (From from) (To to)
  {-# Inline edgeFromTo #-}

instance TermStaticVar (Edge e) (BS1 k I) where
  termStaticVar   _ (IStatic   d) _ = IVariable $ d+1
  termStaticVar   _ (IVariable d) _ = IVariable $ d+1
  termStreamIndex _ _  ix = ix
  {-# Inline [0] termStaticVar #-}
  {-# Inline [0] termStreamIndex #-}

