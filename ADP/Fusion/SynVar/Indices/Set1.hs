
module ADP.Fusion.SynVar.Indices.Set1 where

import Control.Exception (assert)
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

import ADP.Fusion.Core.Set1



-- |
--
-- TODO After this case we should only allow @S@, since we write, in
-- essence, left-linear grammars here.
--
-- TODO we should try to statically assure that @rb==0@ holds always in
-- this case. It should because every other symbol moves to @IVariable@
-- once the number of of reserved bits is @>0@.

instance
  ( IndexHdr s x0 i0 us (BS1 First I) cs c is (BS1 First I)
  ) => AddIndexDense s (us:.BS1 k I) (cs:.c) (is:.BS1 k I) where
  -- This rule should only be active if we have @X -> Y@ rules. Neither @X
  -- -> Y Z@ nor @X -> e Y@ are possible in a left-linear grammar.
  addIndexDenseGo (cs:.c) (vs:.IStatic rb) (lbs:._) (ubs:._) (us:.BS1 uSet uBnd) (is:.BS1 set bnd)
    = map (\(SvS s t y') ->
        let RiBs1I (BS1 cset (Boundary to)) = getIndex (getIdx s) (Proxy :: PRI is (BS1 First I))
        in  assert (cset == 0 && to == (-1)) $ SvS s (t:.BS1 set bnd) (y' :.: RiBs1I (BS1 set bnd)))
    . addIndexDenseGo cs vs lbs ubs us is
    . assert (rb==0)
  -- Deal with @X -> Y e@ type rules.
  addIndexDenseGo (cs:.c) (vs:.IVariable rb) (lbs:._) (ubs:._) (us:.BS1 uSet uBnd) (is:.BS1 set bnd)
    = flatten mk step . addIndexDenseGo cs vs lbs ubs us is
          -- Extract how many bits are already set -- should be zero (!) --
          -- and prepare the list of all possibilities.
          -- In addition, at least one bit should be reserved, hence
          -- @rb>0@. The boundary bit is one of those reserved and
          -- constitutes a mask to be used further down.
    where mk (SvS s t y') =
            let RiBs1I (BS1 cset (Boundary to)) = getIndex (getIdx s) (Proxy :: PRI is (BS1 First I))
                numBits = popCount cset
                stopAt  = numBits - rb + 1
                -- initialize to lowest set, that fullfills the
                -- constraints. The @Boundary@ bit is not a valid bit to
                -- set here!
                initSet  = popShiftL initMask $ 2 ^ (popCount set - rb - numBits) - 1
                initBnd  = Boundary $ lsbZ initSet
            in  assert (numBits == 0 && to == (-1) && rb > 0)
                $ return (SvS s t y', if rb > popCount set then Nothing else Just $ BS1 initSet initBnd)
          step (_, Nothing)
            = return Done
          step (SvS s t y', Just (BS1 nset nbnd)) =
            -- No need to provide @nset .|. getIndex s@ because no bit is
            -- set in @getIndex s@.
            return $ Yield (SvS s (t:.BS1 nset nbnd) (y':.:RiBs1I (BS1 nset nbnd)))
                           ( SvS s t y', setSucc (BS1 0 (-1)) (BS1 initMask initBnd) (BS1 nset nbnd))
          initMask = set `clearBit` getBoundary bnd
          initBnd  = Boundary $ lsbZ initMask
          {-# Inline [0] mk       #-}
          {-# Inline [0] step     #-}
          {-# Inline     initMask #-}
  {-# Inline addIndexDenseGo #-}

{-
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
-}

