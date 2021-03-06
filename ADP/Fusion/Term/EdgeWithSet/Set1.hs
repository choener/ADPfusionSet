
module ADP.Fusion.Term.EdgeWithSet.Set1 where

import Data.Bits
import Data.Strict.Tuple
import Data.Vector.Fusion.Stream.Monadic hiding (flatten)
import Debug.Trace
import Prelude hiding (map,filter)
import Control.Exception (assert)

import ADP.Fusion.Core
import Data.Bits.Ordered
import Data.PrimitiveArray hiding (map)

import ADP.Fusion.Core.Set1
import ADP.Fusion.Term.EdgeWithSet.Type
import ADP.Fusion.Term.Edge.Set1 (EdgeFromTo(..), SetNode(..), NewNode(..))



instance
  ( TmkCtx1 m ls EdgeWithSet (BS1 k t)
  ) => MkStream m (ls :!: EdgeWithSet) (BS1 k t) where
  mkStream (ls :!: EdgeWithSet) sv us is
    = map (\(ss,ee,ii) -> ElmEdgeWithSet ee ii ss)
    . addTermStream1 EdgeWithSet sv us is
    $ mkStream ls (termStaticVar EdgeWithSet sv is) us (termStreamIndex EdgeWithSet sv is)
  {-# Inline mkStream #-}


-- | We need to separate out the two cases of having @BS1 First@ and @BS1
-- Last@ as this changes how we fill the Edge.
--
-- TODO separate out these cases into an Edge-Choice class ...

instance
  ( TstCtx m ts s x0 i0 is (BS1 k I)
  , EdgeFromTo k
  ) => TermStream m (TermSymbol ts EdgeWithSet) s (is:.BS1 k I) where
  -- Begin the edge on @First == b@, and end it somewhere in the set.
  termStream (ts:|EdgeWithSet) (cs:.IStatic r) (us:.u) (is:.BS1 i (Boundary newNode))
    = map (\(TState s ii ee) ->
        let RiBs1I (BS1 cset (Boundary setNode)) = getIndex (getIdx s) (Proxy :: PRI is (BS1 k I))
            (ef:.et) = edgeFromTo (Proxy :: Proxy k) (SetNode setNode) (NewNode newNode)
        in
#if ADPFUSION_DEBUGOUTPUT
            traceShow ("EWSI",i,newNode,'>',cset,setNode,ef,et) $
#endif
            TState s (ii:.:RiBs1I (BS1 i (Boundary newNode)))
                     (ee:.(getBitSet cset:.ef:.et) ) )
    . filter (\(TState s ii ee) ->
        let RiBs1I (BS1 cset (Boundary setNode)) = getIndex (getIdx s) (Proxy :: PRI is (BS1 k I))
        in  popCount cset >= 1)
    . termStream ts cs us is
    -- only insert edges, if there at least two active nodes!
    . staticCheck (popCount i >= 2)
  -- Begin the edge somewhere, because in the variable case we do not end
  -- on @b@
  termStream (ts:|EdgeWithSet) (cs:.IVariable r) (us:.u) (is:.BS1 i b)
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
                  (ef:.et) = edgeFromTo (Proxy :: Proxy k) (SetNode setNode) (NewNode newNode)
              in  return $ Yield (TState s (ii:.:ix) (ee:.(getBitSet cset:.ef:.et)))
                                 (TState s ii ee,cset,setNode,xs)
          {-# Inline [0] mk   #-}
          {-# Inline [0] step #-}
  {-# Inline termStream #-}

-- TODO 17.2.2017 added

instance
  ( TstCtx m ts s x0 i0 is (BS1 k O)
  , EdgeFromTo k
  ) => TermStream m (TermSymbol ts EdgeWithSet) s (is:.BS1 k O) where
  termStream (ts:|EdgeWithSet) (cs:.OStatic r) (us:.u) (is:.BS1 gset (Boundary gbnd))
    = map (\(TState s ii ee) ->
        let RiBs1O (BS1 cset (Boundary cbnd)) = getIndex (getIdx s) (Proxy :: PRI is (BS1 k O))
            (ef:.et) = edgeFromTo (Proxy :: Proxy k) (SetNode gbnd) (NewNode cbnd)
        in
#if ADPFUSION_DEBUGOUTPUT
            traceShow ("EWSO",gset,gbnd,' ',cset,cbnd,ef,et) $
#endif
            TState s (ii:.:RiBs1O (BS1 gset (Boundary gbnd)))
                     (ee:.(getBitSet gset:.ef:.et) ) )
    . termStream ts cs us is
    -- TODO needs to be better!
    . assert (r==0)
    . staticCheck (popCount gset >= 1)

instance
  ( TstCtx m ts s x0 i0 is (BS1 k C)
  , EdgeFromTo k
  ) => TermStream m (TermSymbol ts EdgeWithSet) s (is:.BS1 k C) where


instance TermStaticVar EdgeWithSet (BS1 k I) where
  termStaticVar   _ (IStatic   d) _ = IVariable $ d+1
  termStaticVar   _ (IVariable d) _ = IVariable $ d+1
  termStreamIndex _ _  ix = ix
  {-# Inline [0] termStaticVar #-}
  {-# Inline [0] termStreamIndex #-}

instance TermStaticVar EdgeWithSet (BS1 k O) where
  termStaticVar _ (OStatic  d) _ = ORightOf   $ d+1
  termStaticVar _ (ORightOf d) _ = OFirstLeft $ d+1
  termStreamIndex _ _  ix = ix
  {-# Inline [0] termStaticVar #-}
  {-# Inline [0] termStreamIndex #-}

