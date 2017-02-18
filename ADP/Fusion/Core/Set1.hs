
-- | Bitsets @BS1 i@ are bitsets where one of the active bits is annotated
-- as the first or last bit that has been set. In principle, being first or
-- last is exchangeable, but is made explicit to allow for type-different
-- sets.

module ADP.Fusion.Core.Set1 where

import Data.Proxy
import Data.Vector.Fusion.Stream.Monadic (singleton,filter,enumFromStepN,map,unfoldr)
import Debug.Trace
import Prelude hiding (map,filter)
import Data.Bits
import Data.Bits.Ordered

import Data.PrimitiveArray hiding (map)

import ADP.Fusion.Core.Classes
import ADP.Fusion.Core.Multi



instance RuleContext (BS1 i I) where
  type Context (BS1 i I) = InsideContext Int
  initialContext _ = IStatic 0
  {-# Inline initialContext #-}

instance RuleContext (BS1 i O) where
  type Context (BS1 i O) = OutsideContext Int
  initialContext _ = OStatic 0
  {-# Inline initialContext #-}

newtype instance RunningIndex (BS1 i I) = RiBs1I (BS1 i I)

-- Only allow linear languages for now!

newtype instance RunningIndex (BS1 i O) = RiBs1O (BS1 i O)

instance
  ( Monad m
  ) => MkStream m S (BS1 i I) where
  -- In case of @X -> ε@ or @X -> Singleton@, we have a static case here
  -- and allow the rule to succeed.
  -- TODO is this right? I don't think so
  mkStream S (IStatic z) u sk@(BS1 s (Boundary k))
    = let pc = popCount s
      in  staticCheck (pc <= 1 && pc == z) . singleton . ElmS . RiBs1I $ sk
  --
  mkStream S (IVariable rp) u sk@(BS1 s (Boundary k))
    = staticCheck (popCount s >= rp) . singleton . ElmS . RiBs1I $ BS1 0 (Boundary $ -1)
  {-# Inline mkStream #-}

instance
  ( Monad m
  ) => MkStream m S (BS1 i O) where
  mkStream S (OStatic z) (BS1 uset (Boundary ubnd)) (BS1 cset (Boundary cbnd))
    = let pcc = popCount cset
          pcu = popCount uset
      in  staticCheck (pcu - pcc <= z && z <= 1) . singleton . ElmS . RiBs1O $ BS1 cset (Boundary cbnd)
  mkStream S (OFirstLeft z) (BS1 uset (Boundary ubnd)) (BS1 cset (Boundary cbnd))
    = let ------------V--- TODO ???
      in
#if ADPFUSION_DEBUGOUTPUT
          traceShow "O" .
#endif
          staticCheck True . singleton . ElmS . RiBs1O $ BS1 uset (Boundary $ -1)
  {-# Inline mkStream #-}

instance (MinSize c) => TableStaticVar u c (BS1 s I) where
  tableStaticVar _ c (IStatic   k) _ = IVariable $ k + minSize c
  tableStaticVar _ c (IVariable k) _ = IVariable $ k + minSize c
  tableStreamIndex _ c _ z = z
  {-# Inline tableStaticVar #-}
  {-# Inline tableStreamIndex #-}

instance (MinSize c) => TableStaticVar u c (BS1 s O) where
  tableStaticVar   _ _ (OStatic  d) _ = OFirstLeft d
  tableStaticVar   _ _ (ORightOf d) _ = OFirstLeft d
  tableStreamIndex _ c _ z = z
  {-# Inline tableStaticVar #-}
  {-# Inline tableStreamIndex #-}

