
module ADP.Fusion.Term.EdgeWithSet.EdgeBoundary where

import Data.Bits
import Data.Strict.Tuple
import Data.Vector.Fusion.Stream.Monadic hiding (flatten)
import Debug.Trace
import Prelude hiding (map)

import ADP.Fusion.Core
import Data.Bits.Ordered
import Data.PrimitiveArray hiding (map)

import ADP.Fusion.Core.EdgeBoundary
import ADP.Fusion.Term.EdgeWithSet.Type



instance
  ( TmkCtx1 m ls EdgeWithSet (EdgeBoundary k)
  ) => MkStream m (ls :!: EdgeWithSet) (EdgeBoundary k) where
  mkStream (ls :!: EdgeWithSet) sv us is
    = map (\(ss,ee,ii) -> ElmEdgeWithSet ee ii ss)
    . addTermStream1 EdgeWithSet sv us is
    $ mkStream ls (termStaticVar EdgeWithSet sv is) us (termStreamIndex EdgeWithSet sv is)
  {-# Inline mkStream #-}

-- Only allow an edge between @from /= to@

instance
  ( TstCtx m ts s x0 i0 is (EdgeBoundary I)
  ) => TermStream m (TermSymbol ts EdgeWithSet) s (is:.EdgeBoundary I) where
  termStream (ts:|EdgeWithSet) (cs:._) (us:.u) (is:.(from :-> to))
    = map (\(TState s ii ee) ->
        let RiEBI cset _ = getIndex (getIdx s) (Proxy :: PRI is (EdgeBoundary I))
        in  TState s (ii:.:RiEBI (cset `setBit` to) (from :-> to))
                     (ee:.(getBitSet cset:.From from:.To to)) )
    . termStream ts cs us is
    . staticCheck (from /= to)
  {-# Inline termStream #-}



instance TermStaticVar EdgeWithSet (EdgeBoundary I) where
  termStaticVar   _ (IStatic   d) _ = IVariable $ d+1
  termStaticVar   _ (IVariable d) _ = IVariable $ d+1
  termStreamIndex _ _  ix = ix
  {-# Inline [0] termStaticVar #-}
  {-# Inline [0] termStreamIndex #-}

