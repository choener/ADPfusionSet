
-- | 

module ADP.Fusion.Core.EdgeBoundary where

import Data.Vector.Fusion.Stream.Monadic (singleton)
import Data.Bits (zeroBits)

import Data.PrimitiveArray hiding (map)

import ADP.Fusion.Core.Classes
import ADP.Fusion.Core.Multi



instance RuleContext (EdgeBoundary I) where
  type Context (EdgeBoundary I) = InsideContext Int
  initialContext _ = IStatic 0
  {-# Inline initialContext #-}

instance RuleContext (EdgeBoundary C) where
  type Context (EdgeBoundary C) = ExtComplementContext ()
  initialContext _ = CStatic ()
  {-# Inline initialContext #-}

data instance RunningIndex (EdgeBoundary I) = RiEBI !(BitSet I) !(EdgeBoundary I)

data instance RunningIndex (EdgeBoundary C) = RiEBC !(BitSet C) !(EdgeBoundary C)

instance
  ( Monad m
  ) => MkStream m S (EdgeBoundary I) where
  mkStream S _ u k
    = singleton . ElmS $ RiEBI zeroBits k
  {-# Inline mkStream #-}

instance
  ( Monad m
  ) => MkStream m S (EdgeBoundary C) where
  mkStream S _ u k
    = singleton . ElmS $ RiEBC zeroBits k
  {-# Inline mkStream #-}

instance TableStaticVar u c (EdgeBoundary I) where
  tableStaticVar _ c (IStatic   k) _ = IVariable k
  tableStaticVar _ c (IVariable k) _ = IVariable k
  tableStreamIndex _ c _ z = z
  {-# Inline tableStaticVar #-}
  {-# Inline tableStreamIndex #-}

instance TableStaticVar u c (EdgeBoundary C) where
  tableStaticVar _ _ comp _ = comp
  tableStreamIndex _ c _ z = z
  {-# Inline tableStaticVar #-}
  {-# Inline tableStreamIndex #-}

