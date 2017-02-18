
module ADP.Fusion.Term.Epsilon.Set1 where

import Data.Proxy
import Data.Strict.Tuple
import Data.Vector.Fusion.Stream.Monadic as S
import Prelude hiding (map)
import Debug.Trace

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
  termStream (ts:|Epsilon) (cs:.IStatic r) (us:.BS1 uset ubnd) (is:.BS1 cset cbnd)
    = map (\(TState s ii ee) ->
#if ADPFUSION_DEBUGOUTPUT
            traceShow ("Empty/BS1/I",BS1 uset ubnd,BS1 cset cbnd) $
#endif
            TState s (ii:.:RiBs1I (BS1 0 0)) (ee:.())
          )
    . termStream ts cs us is
    . staticCheck (cset == 0)
  {-# Inline termStream #-}

instance
  ( TstCtx m ts s x0 i0 is (BS1 k O)
  ) => TermStream m (TermSymbol ts Epsilon) s (is:.BS1 k O) where
  termStream (ts:|Epsilon) (cs:.OStatic r) (us:.BS1 uset ubnd) (is:.BS1 cset cbnd)
    = map (\(TState s ii ee) ->
#if ADPFUSION_DEBUGOUTPUT
            traceShow ("Empty/BS1/O",BS1 uset ubnd,BS1 cset cbnd) $
#endif
            TState s (ii:.:RiBs1O (BS1 cset cbnd)) (ee:.())
          )
    . termStream ts cs us is
    . staticCheck (uset == cset)
  {-# Inline termStream #-}

instance TermStaticVar Epsilon (BS1 k I) where
  termStaticVar _ sv _ = sv
  termStreamIndex _ _ b = b
  {-# Inline [0] termStaticVar #-}
  {-# Inline [0] termStreamIndex #-}

instance TermStaticVar Epsilon (BS1 k O) where
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

