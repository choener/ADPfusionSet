
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
  ( TmkCtx1 m ls (Singleton v) (BS1 k t)
  ) => MkStream m (ls :!: Singleton v) (BS1 k t) where
  mkStream (ls :!: Singleton f) sv us is
    = map (\(ss,ee,ii) -> ElmSingleton ee ii ss)
    . addTermStream1 (Singleton f) sv us is
    $ mkStream ls (termStaticVar (Singleton f) sv is) us (termStreamIndex (Singleton f) sv is)
  {-# Inline mkStream #-}

instance
  ( TstCtx m ts s x0 i0 is (BS1 k I)
  ) => TermStream m (TermSymbol ts (Singleton v)) s (is:.BS1 k I) where
  termStream (ts:|Singleton f) (cs:.IStatic r) (us:.u) (is:.BS1 i b)
    = map (\(TState s ii ee) -> let Boundary bb = b in
              TState s (ii:.:RiBs1I (BS1 i b)) (ee:.f bb) )
    . termStream ts cs us is
    . staticCheck (popCount i == 1)
  {-# Inline termStream #-}

instance TermStaticVar (Singleton v) (BS1 k I) where
  termStaticVar   _ (IStatic   d) _ = IStatic   $ d+1
  termStaticVar   _ (IVariable d) _ = IVariable $ d+1
  termStreamIndex _ _  ix = ix
  {-# Inline [0] termStaticVar #-}
  {-# Inline [0] termStreamIndex #-}

