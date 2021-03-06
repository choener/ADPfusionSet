
module ADP.Fusion.Term.Epsilon.Set2 where

import Data.Proxy
import Data.Strict.Tuple
import Data.Vector.Fusion.Stream.Monadic as S
import Prelude hiding (map)

import ADP.Fusion.Core
import Data.Bits.Ordered
import Data.PrimitiveArray hiding (map)

import ADP.Fusion.Core.Set2



-- ** Two boundaries

instance
  ( TmkCtx1 m ls Epsilon (BS2 First Last i)
  ) => MkStream m (ls :!: Epsilon) (BS2 First Last i) where
  mkStream (ls :!: Epsilon) sv us is
    = map (\(ss,ee,ii) -> ElmEpsilon ii ss)
    . addTermStream1 Epsilon sv us is
    $ mkStream ls (termStaticVar Epsilon sv is) us (termStreamIndex Epsilon sv is)
  {-# Inline mkStream #-}

instance
  ( TstCtx m ts s x0 i0 is (BS2 First Last I)
  ) => TermStream m (TermSymbol ts Epsilon) s (is:.BS2 First Last I) where
  termStream (ts:|Epsilon) (cs:.IStatic r) (us:.u) (is:.BS2 bs _ _)
    = map (\(TState s ii ee) ->
              TState s (ii:.:RiBs2I (BS2 0 0 0)) (ee:.()) )
    . termStream ts cs us is
    . staticCheck (bs==0)
  {-# Inline termStream #-}

instance
  ( TstCtx m ts s x0 i0 is (BS2 First Last O)
  ) => TermStream m (TermSymbol ts Epsilon) s (is:.BS2 First Last O) where
  termStream (ts:|Epsilon) (cs:.OStatic r) (us:.BS2 ub uf ul) (is:.BS2 bs f l)
    = map (\(TState s ii ee) ->
              let io = getIndex (getIdx s) (Proxy :: PRI is (BS2 First Last O))
              in  TState s (ii:.:io) (ee:.()) )
    . termStream ts cs us is
    . staticCheck (ub==bs)
  {-# Inline termStream #-}


{-

instance TermStaticVar Epsilon (BitSet I) where
  termStaticVar _ sv _ = sv
  termStreamIndex _ _ b = b
  {-# Inline [0] termStaticVar #-}
  {-# Inline [0] termStreamIndex #-}

instance TermStaticVar Epsilon (BitSet O) where
  termStaticVar _ sv _ = sv
  termStreamIndex _ _ b = b
  {-# Inline [0] termStaticVar #-}
  {-# Inline [0] termStreamIndex #-}

-}

