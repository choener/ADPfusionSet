
module ADP.Fusion.Term.PeekIndex.Set1 where

import Data.Strict.Tuple
import Data.Vector.Fusion.Stream.Monadic hiding (flatten)
import Debug.Trace
import Prelude hiding (map)

import Data.PrimitiveArray hiding (map)

import ADP.Fusion.Core.Classes
import ADP.Fusion.Core.Multi



data PeekIndex i = PeekIndex

instance Build (PeekIndex i)

instance
  ( Element ls i
  ) => Element (ls :!: PeekIndex i) i where
    data Elm (ls :!: PeekIndex i) i = ElmPeekIndex !i !(RunningIndex i) !(Elm ls i)
    type Arg (ls :!: PeekIndex i)   = Arg ls :. i
    getArg (ElmPeekIndex x _  ls)    = getArg ls :. x
    getIdx (ElmPeekIndex _ i  _ )    = i
    {-# Inline getArg #-}
    {-# Inline getIdx #-}

deriving instance (Show i, Show (RunningIndex i), Show (Elm ls i)) => Show (Elm (ls :!: PeekIndex i) i)

type instance TermArg (PeekIndex i) = i

instance
  ( TmkCtx1 m ls (PeekIndex (BS1 k t)) (BS1 k t)
  ) => MkStream m (ls :!: PeekIndex (BS1 k t)) (BS1 k t) where
  mkStream (ls :!: PeekIndex) sv us is
    = map (\(ss,ee,ii) -> ElmPeekIndex ee ii ss)
    . addTermStream1 PeekIndex sv us is
    $ mkStream ls (termStaticVar (PeekIndex :: PeekIndex (BS1 k t)) sv is) us (termStreamIndex (PeekIndex :: PeekIndex (BS1 k t)) sv is)
  {-# Inline mkStream #-}

instance
  ( TstCtx m ts s x0 i0 is (BS1 k I)
  ) => TermStream m (TermSymbol ts (PeekIndex (BS1 k I))) s (is:.BS1 k I) where
--  termStream (ts:|PeekIndex) (cs:.IStatic r) (us:.u) (is:.BS1 i b)
--    = map (\(TState s ii ee) -> let Boundary bb = b in
--              TState s (ii:.:RiBs1I (BS1 i b)) (ee:.(0:.To bb)) )
--    . termStream ts cs us is
--    . staticCheck (popCount i == 1)
--  {-# Inline termStream #-}

instance TermStaticVar (PeekIndex (BS1 k i)) (BS1 k i) where
  termStaticVar   _ isv _ = isv
  termStreamIndex _ _  ix = ix
  {-# Inline [0] termStaticVar #-}
  {-# Inline [0] termStreamIndex #-}

