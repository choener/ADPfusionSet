
module ADP.Fusion.SynVar.Indices.Set2 where

import Data.Proxy
import Data.Vector.Fusion.Stream.Monadic (map,Stream,head,mapM,Step(..))
import Data.Vector.Fusion.Util (delay_inline)
import Debug.Trace
import Prelude hiding (map,head,mapM)
import Data.Bits.Extras
import Data.Bits

import ADP.Fusion.Core
import Data.Bits.Ordered
import Data.PrimitiveArray hiding (map)

import ADP.Fusion.Core.Set2



instance
  ( IndexHdr s x0 i0 us (BS2 First Last I) cs c is (BS2 First Last I)
  ) => AddIndexDense s (us:.BS2 First Last I) (cs:.c) (is:.BS2 First Last I) where
  -- In the static case the following holds:
  -- 1) First comes from the incoming index
  -- 2) Last is the Last actually provided to us
  -- 3) the lookup bits for the table are just the xor of the incoming and
  -- the given bits. Note that First-Last are overlapping between two
  -- symbols.
  addIndexDenseGo (cs:.c) (vs:.IStatic Set2Fixed) (lbs:._) (ubs:._) (us:.BS2 uSet _ _) (is:.BS2 iSet frst lst)
    = map (\(SvS s t y') ->
        let RiBs2I (BS2 σ α ο) = getIndex (getIdx s) (Proxy :: PRI is (BS2 First Last I))
            α' = α -- if α == (-1) then frst else α -- TODO test on (-1) var/static handling in S?
            tblSet = ((σ `xor` iSet) .&. uSet) `setBit` getIter α'
            nowSet = (σ .|. iSet)
            --                   v-- where the left part stopped, we start
        in  SvS s (t:.BS2 tblSet (Iter $ getIter ο) lst) (y' :.: RiBs2I (BS2 nowSet frst lst))
            --                                      ^-- where we stop
      )
    . addIndexDenseGo cs vs lbs ubs us is
  addIndexDenseGo (cs:.c) (vs:.IStatic (Set2First rb)) (lbs:._) (ubs:._) (us:.BS2 uSet _ _) (is:.BS2 iSet frst lst)
    = flatten mk step . addIndexDenseGo cs vs lbs ubs us is
    where mk svs = return svs -- TODO get smallest set with @2^(popcount uset-rb)@ bits and start rolling
          step = undefined
          -- We have a single step to make as there is no other symbol to
          -- the right of us, which could require 
          {-# Inline [0] mk   #-}
          {-# Inline [0] step #-}
  -- We are variable and need to go through all available bits. However, we
  -- need to keep @rb@ bits free for other objects.
  addIndexDenseGo (cs:.c) (vs:.IVariable rb) (lbs:._) (ubs:._) (us:.u) (is:.i)
    = flatten mk step . addIndexDenseGo cs vs lbs ubs us is
    where mk svs = return (svs, undefined)
          step = undefined
          {-# Inline [0] mk   #-}
          {-# Inline [0] step #-}
  {-# Inline addIndexDenseGo #-}

