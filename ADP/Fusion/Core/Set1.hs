
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



{-
data Set1Context
  = Set1Fixed
  -- ^ For the right, static elements in a production rule.
  | Set1Var !Int
  -- ^ TODO write me
  deriving (Eq,Show)
-}

instance RuleContext (BS1 i I) where
  type Context (BS1 i I) = InsideContext Int
  initialContext _ = IStatic 0
  {-# Inline initialContext #-}

newtype instance RunningIndex (BS1 i I) = RiBs1I (BS1 i I)

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

instance (MinSize c) => TableStaticVar u c (BS1 s I) where
  tableStaticVar _ c (IStatic   k) _ = IVariable $ k + minSize c
  tableStaticVar _ c (IVariable k) _ = IVariable $ k + minSize c
  tableStreamIndex _ c _ z = z
  {-# Inline tableStaticVar #-}
  {-# Inline tableStreamIndex #-}

