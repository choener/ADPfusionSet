
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
  ( TstCtx m ts s x0 i0 is (BS1 First I)
  ) => TermStream m (TermSymbol ts (Edge v)) s (is:.BS1 First I) where
  -- Begin the edge on @First == b@, and end it somewhere in the set.
  termStream (ts:|Edge f) (cs:.IStatic r) (us:.u) (is:.BS1 i (Boundary from))
    = map (\(TState s ii ee) ->
        let RiBs1I (BS1 cset (Boundary to)) = getIndex (getIdx s) (Proxy :: PRI is (BS1 First I))
        in  TState s (ii:.:RiBs1I (BS1 i (Boundary from))) (ee:.f (From from) (To to)) )
    . termStream ts cs us is
  -- Begin the edge somewhere, because in the variable case we do not end
  -- on @b@
  termStream (ts:|Edge f) (cs:.IVariable r) (us:.u) (is:.BS1 i b)
    = flatten mk step . termStream ts cs us is
          -- get us the inner set, build an edge @avail -> to@
    where mk tstate@(TState s ii ee) =
            let RiBs1I (BS1 cset (Boundary cto)) = getIndex (getIdx s) (Proxy :: PRI is (BS1 First I))
                avail = activeBitsL $ (i .&. complement cset) `clearBit` getBoundary b
            in  return $ (tstate,cset,cto,avail)
          step (_,_,_,[]) = return $ Done
          step (TState s ii ee,cset,to,(from:xs)) =
            let ix = RiBs1I $ BS1 (cset `setBit` from) (Boundary from)
            in  return $ Yield (TState s (ii:.:ix) (ee:.f (From from) (To to))) (TState s ii ee,cset,to,xs)
          {-# Inline [0] mk   #-}
          {-# Inline [0] step #-}
  {-# Inline termStream #-}

instance TermStaticVar (Edge e) (BS1 k I) where
  termStaticVar   _ (IStatic   d) _ = IVariable $ d+1
  termStaticVar   _ (IVariable d) _ = IVariable $ d+1
  termStreamIndex _ _  ix = ix
  {-# Inline [0] termStaticVar #-}
  {-# Inline [0] termStreamIndex #-}

