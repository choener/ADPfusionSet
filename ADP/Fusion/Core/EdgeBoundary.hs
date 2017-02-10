
-- | 

module ADP.Fusion.Core.EdgeBoundary where

import Data.Vector.Fusion.Stream.Monadic (singleton)

import Data.PrimitiveArray hiding (map)

import ADP.Fusion.Core.Classes
import ADP.Fusion.Core.Multi



-- |
--
-- TODO Combine with Term.Edge.Type?

data EdgeBoundary k = !Int :-> !Int

instance RuleContext (EdgeBoundary I) where
  type Context (EdgeBoundary I) = InsideContext Int
  initialContext _ = IStatic 0
  {-# Inline initialContext #-}

data instance RunningIndex (EdgeBoundary I) = RiEBI !Int !(EdgeBoundary I)

instance
  ( Monad m
  ) => MkStream m S (EdgeBoundary I) where
  mkStream S _ u k
    = singleton . ElmS $ RiEBI 0 k
  {-# Inline mkStream #-}

instance TableStaticVar u c (EdgeBoundary I) where
  tableStaticVar _ c (IStatic   k) _ = IVariable k
  tableStaticVar _ c (IVariable k) _ = IVariable k
  tableStreamIndex _ c _ z = z
  {-# Inline tableStaticVar #-}
  {-# Inline tableStreamIndex #-}

