
-- | Core structures for using 'Boundary' indices. These are isomorphic to
-- @Int@ but are to be used to indicate "boundary" elements in sets.
--
-- Immediate use is given, if one for example wants to extract posterior
-- scores for each possible endpoint in a set.

module ADP.Fusion.Core.Boundary where

import Data.Vector.Fusion.Stream.Monadic (singleton)

import Data.PrimitiveArray hiding (map)

import ADP.Fusion.Core.Classes
import ADP.Fusion.Core.Multi



instance RuleContext (Boundary i I) where
  type Context (Boundary i I) = InsideContext ()
  initialContext _ = IStatic ()
  {-# Inline initialContext #-}

newtype instance RunningIndex (Boundary i I) = RiBI (Boundary i I)

instance
  ( Monad m
  ) => MkStream m S (Boundary i I) where
  -- In case of @X -> ε@ or @X -> Singleton@, we have a static case here
  -- and allow the rule to succeed.
  -- TODO is this right? I don't think so
  mkStream S _ u k
    = singleton . ElmS . RiBI $ k
  {-# Inline mkStream #-}

instance TableStaticVar u c (Boundary i I) where
  tableStaticVar _ c _ _ = IVariable ()
  tableStreamIndex _ c _ z = z
  {-# Inline tableStaticVar #-}
  {-# Inline tableStreamIndex #-}

