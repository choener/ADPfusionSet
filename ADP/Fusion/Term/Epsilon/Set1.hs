
module ADP.Fusion.Term.Epsilon.Set1 where

import Data.Proxy
import Data.Strict.Tuple
import Data.Vector.Fusion.Stream.Monadic as S
import Prelude hiding (map)

import ADP.Fusion.Core
import Data.Bits.Ordered
import Data.PrimitiveArray hiding (map)

import ADP.Fusion.Core.Set1



instance
  ( TmkCtx1 m ls Epsilon (BS1 k t)
  ) => MkStream m (ls :!: Epsilon) (BS1 k t) where
  mkStream (ls :!: Epsilon) sv us is
    = map (\(ss,ee,ii) -> ElmEpsilon ii ss)
    . addTermStream1 Epsilon sv us is
    $ mkStream ls (termStaticVar Epsilon sv is) us (termStreamIndex Epsilon sv is)
  {-# Inline mkStream #-}

instance
  ( TstCtx m ts s x0 i0 is (BS1 k I)
  ) => TermStream m (TermSymbol ts Epsilon) s (is:.BS1 k I) where
  termStream (ts:|Epsilon) (cs:.IStatic r) (us:.u) (is:.BS1 i _)
    = map (\(TState s ii ee) ->
              TState s (ii:.:RiBs1I (BS1 i $ -1)) (ee:.()) )
    . termStream ts cs us is
    . staticCheck (i==0)
  {-# Inline termStream #-}

{-
instance
  ( TstCtx m ts s x0 i0 is (BS1 i O)
  ) => TermStream m (TermSymbol ts Epsilon) s (is:.BitSet O) where
  termStream (ts:|Epsilon) (cs:.OStatic r) (us:.u) (is:.i)
    = map (\(TState s ii ee) ->
              TState s (ii:.:RiBsO u u) (ee:.()) )
    . termStream ts cs us is
    . staticCheck (i==u)
  {-# Inline termStream #-}
-}

instance TermStaticVar Epsilon (BS1 k I) where
  termStaticVar _ sv _ = sv
  termStreamIndex _ _ b = b
  {-# Inline [0] termStaticVar #-}
  {-# Inline [0] termStreamIndex #-}

{-
instance TermStaticVar Epsilon (BitSet O) where
  termStaticVar _ sv _ = sv
  termStreamIndex _ _ b = b
  {-# Inline [0] termStaticVar #-}
  {-# Inline [0] termStreamIndex #-}
-}
