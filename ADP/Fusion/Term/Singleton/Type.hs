
-- | Type definition for singleton terminal symbols.

module ADP.Fusion.Term.Singleton.Type where

import Data.Strict.Tuple

import Data.PrimitiveArray

import ADP.Fusion.Core.Classes
import ADP.Fusion.Core.Multi



-- | A singleton vertex is successfully parsed only if no other vertex is
-- active yet. In particular, this allows us to insert "starting" points
-- into graphs that mostly deal with edges.

data Singleton v where
  Singleton :: (Int -> v) -> Singleton v

instance Build (Singleton v)

instance
  ( Element ls i
  ) => Element (ls :!: Singleton v) i where
    data Elm (ls :!: Singleton v) i = ElmSingleton !v !(RunningIndex i) (Elm ls i)
    type Arg (ls :!: Singleton v)   = Arg ls :. v
    getArg (ElmSingleton v _ ls) = getArg ls :. v
    getIdx (ElmSingleton _ i _ ) = i
    {-# Inline getArg #-}
    {-# Inline getIdx #-}

deriving instance (Show i, Show (RunningIndex i), Show v, Show (Elm ls i)) => Show (Elm (ls :!: Singleton v) i)

type instance TermArg (Singleton v) = v

