
-- | The @Context@ for a @BitSet@ is the number of bits we should reserve
-- for the more right-most symbols, which request a number of reserved
-- bits.

module ADP.Fusion.Core.Set2 where

import Data.Proxy
import Data.Vector.Fusion.Stream.Monadic (singleton,filter,enumFromStepN,map,unfoldr)
import Debug.Trace
import Prelude hiding (map,filter)
import Data.Bits
import Data.Bits.Ordered

import Data.PrimitiveArray hiding (map)

import ADP.Fusion.Core.Classes
import ADP.Fusion.Core.Multi



-- | When dealing with rules @X -> Y Z@, we need to annotate which of the
-- @First@ and @Last@ nodes are allowed to move freely.
--
-- @X -> a@ fixes a single node as @Singleton@.
--
-- @X -> Y a@ with @Edge a@ sets @Last X == Last a@ and allows @Y@ to
-- choose @Last Y@ freely. In addition, @Last Y == First a@.
--
-- @X -> a Y@ with @Edge a@ set @First X == First a@ and allows @a@ to
-- choose @Last a@ freely. @Last a == First Y@.
--
-- @ X -> Y Z@
--
-- ... freely always means freely within the @interior X@ part.

data Set2Context
  = Set2Fixed
  -- ^ completely fixed set, for the right-most element. Here, the l.h.s.
  -- completely determines the first and last node. However, @First@ needs
  -- to be taken from as the @Last Y@ element from @X -> Y Z@, as well as
  -- calculating which free bits to take as @interior X \ interior Y + Last
  -- Y@.
  | Set2MoveLast !Int
  -- ^ The @First@ element is fixed by the symbol immediately to the left,
  -- the @Last@ element we can move freely. The @Int@ gives the number of
  -- bits we have to keep free for elements more to the right.
--  | Set2Var !Int
--  -- ^ only the @First@ element is fixed, @Last@ will move around. In
--  -- addition, at least @Int@ bits are free.
  deriving (Eq)

instance RuleContext (BS2 First Last I) where
  type Context (BS2 First Last I) = InsideContext Set2Context
  initialContext _ = IStatic Set2Fixed
  {-# Inline initialContext #-}

instance RuleContext (BS2 First Last O) where
  type Context (BS2 First Last O) = OutsideContext Set2Context
  initialContext _ = OStatic Set2Fixed
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
--  mkStream S (IStatic rp) u sij@(BS2 s (Iter i) _)
--    = staticCheck (popCount s == 0 && rp == 0) . singleton . ElmS . RiBs2I $ BS2 0 (Iter i) (Iter i)
  -- In the variable case, no bits are set. In addition we set first and
  -- last to @-1@ to denote that not anything has been set.
  -- ------
  -- No bits are set, but if @First@ is to be used, it should be @i@.
  mkStream S (IVariable rp) u sij@(BS2 s (Iter i) _)
    = staticCheck (popCount s >= rp) . singleton . ElmS . RiBs2I $ BS2 0 (Iter i) (Iter i)
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

