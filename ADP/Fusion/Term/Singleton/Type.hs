
-- | Type definition for singleton terminal symbols.

module ADP.Fusion.Term.Singleton.Type where

import Data.Strict.Tuple

import Data.PrimitiveArray
import ADP.Fusion.Term.Edge.Type (To(..))

import ADP.Fusion.Core.Classes
import ADP.Fusion.Core.Multi



-- | A singleton vertex is successfully parsed only if no other vertex is
-- active yet. In particular, this allows us to insert "starting" points
-- into graphs that mostly deal with edges. As a parsing symbol, it
-- provides an @Int@ which is the node index.

data Singleton = Singleton

instance Build Singleton

instance
  ( Element ls i
  ) => Element (ls :!: Singleton) i where
    data Elm (ls :!: Singleton) i = ElmSingleton !(Int:.To) !(RunningIndex i) (Elm ls i)
    type Arg (ls :!: Singleton)   = Arg ls :. (Int:.To)
    getArg (ElmSingleton v _ ls) = getArg ls :. v
    getIdx (ElmSingleton _ i _ ) = i
    {-# Inline getArg #-}
    {-# Inline getIdx #-}

deriving instance (Show i, Show (RunningIndex i), Show (Elm ls i)) => Show (Elm (ls :!: Singleton) i)

type instance TermArg Singleton = (Int:.To)

