
-- | Singleton vertices are only introduced into a set structure, if no
-- vertex has been placed yet.
--
-- We explicitly check that @X -> s@ is the only allowed rule, with @s ==
-- Singleton@, apart from introducing "deletion" symbols like @X -> - s@.

module ADP.Fusion.Term.Singleton.Set1 where

import Data.Bits
import Data.Strict.Tuple
import Data.Vector.Fusion.Stream.Monadic hiding (flatten)
import Debug.Trace
import Prelude hiding (map)

import ADP.Fusion.Core
import Data.Bits.Ordered
import Data.PrimitiveArray hiding (map)

import ADP.Fusion.Core.Set1
import ADP.Fusion.Term.Singleton.Type



instance
  ( TmkCtx1 m ls Singleton (BS1 k t)
  ) => MkStream m (ls :!: Singleton) (BS1 k t) where
  mkStream (ls :!: Singleton) sv us is
    = map (\(ss,ee,ii) -> ElmSingleton ee ii ss)
    . addTermStream1 Singleton sv us is
    $ mkStream ls (termStaticVar Singleton sv is) us (termStreamIndex Singleton sv is)
  {-# Inline mkStream #-}

instance
  ( TstCtx m ts s x0 i0 is (BS1 k I)
  ) => TermStream m (TermSymbol ts Singleton) s (is:.BS1 k I) where
  termStream (ts:|Singleton) (cs:.IStatic r) (us:.u) (is:.BS1 i b)
    = map (\(TState s ii ee) -> let Boundary bb = b in
              TState s (ii:.:RiBs1I (BS1 i b)) (ee:.bb) )
    . termStream ts cs us is
    . staticCheck (popCount i == 1)
  {-# Inline termStream #-}

-- |
--
-- TODO 17.2.2017 added; probably wrong together with the syntactic
-- variable instance in subtle ways.

instance
  ( TstCtx m ts s x0 i0 is (BS1 k O)
  ) => TermStream m (TermSymbol ts Singleton) s (is:.BS1 k O) where
  termStream (ts:|Singleton) (cs:.OStatic r) (us:.BS1 uset ubnd) (is:.BS1 cset cbnd)
    = map (\(TState s ii ee) -> TState s (ii:.:RiBs1O (BS1 cset cbnd)) (ee:.getBoundary cbnd) )
    . termStream ts cs us is
    . staticCheck (popCount uset - 1 == popCount cset)
    -- TODO remove after thought out!
    . staticCheck False
  {-# Inline termStream #-}

instance TermStaticVar Singleton (BS1 k I) where
  termStaticVar   _ (IStatic   d) _ = IStatic   $ d+1
  termStaticVar   _ (IVariable d) _ = IVariable $ d+1
  termStreamIndex _ _  ix = ix
  {-# Inline [0] termStaticVar #-}
  {-# Inline [0] termStreamIndex #-}

instance TermStaticVar Singleton (BS1 k O) where
  termStaticVar _ (OStatic d) _ = ORightOf $ d+1
  termStreamIndex _ _  ix = ix
  {-# Inline [0] termStaticVar #-}
  {-# Inline [0] termStreamIndex #-}

