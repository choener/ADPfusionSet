
-- | The @Context@ for a @BitSet@ is the number of bits we should reserve
-- for the more right-most symbols, which request a number of reserved
-- bits.

module ADP.Fusion.Core.Set where

import Data.Proxy
import Data.Vector.Fusion.Stream.Monadic (singleton,filter,enumFromStepN,map,unfoldr)
import Debug.Trace
import Prelude hiding (map,filter)
import Data.Bits
import Data.Bits.Ordered

import Data.PrimitiveArray hiding (map)

import ADP.Fusion.Core.Classes
import ADP.Fusion.Core.Multi



instance RuleContext (BS2 First Last I) where
  type Context (BS2 First Last I) = InsideContext Int
  initialContext _ = IStatic 0
  {-# Inline initialContext #-}

instance RuleContext (BS2 First Last O) where
  type Context (BS2 First Last O) = OutsideContext ()
  initialContext _ = OStatic ()
  {-# Inline initialContext #-}

instance RuleContext (BS2 First Last C) where
  type Context (BS2 First Last C) = ComplementContext
  initialContext _ = Complemented
  {-# Inline initialContext #-}

newtype instance RunningIndex (BS2 First Last I) = RiBs2I (BS2 First Last I)

data instance RunningIndex (BS2 First Last O) = RiBs2O !(BS2 First Last O) !(BS2 First Last O)

data instance RunningIndex (BS2 First Last C) = RiBs2C !(BS2 First Last C) !(BS2 First Last C)



instance
  ( Monad m
  ) => MkStream m S (BS2 First Last I) where
  mkStream S (IStatic rp) u sij@(BS2 s (Iter i) _)
    = staticCheck (popCount s == 0 && rp == 0) . singleton . ElmS . RiBs2I $ BS2 0 (Iter i) (Iter i)
  -- In this case, we take 
  mkStream S (IVariable rp) u sij@(BS2 s (Iter i) _)
    = undefined -- staticCheck (popCount s >= rp) . singleton . ElmS . RiBs2I $ BS2 0 (Iter i) (Iter i)
  {-# Inline mkStream #-}

instance
  ( Monad m
  ) => MkStream m S (BS2 First Last O) where
  mkStream = error "Core.Set.hs :: MkStream S BS2 O"

instance
  ( Monad m
  ) => MkStream m S (BS2 First Last C) where
  mkStream = error "Core.Set.hs :: MkStream S BS2 C"



-- | An undefined bitset with 2 interfaces.

undefbs2i :: BS2 f l t
undefbs2i = BS2 (-1)  (-1) (-1)
{-# Inline undefbs2i #-}

undefi :: Interface i
undefi = (-1)
{-# Inline undefi #-}

-- | We sometimes need 

data ThisThatNaught a b = This a | That b | Naught

