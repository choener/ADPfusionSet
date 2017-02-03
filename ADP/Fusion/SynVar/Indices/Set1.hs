
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



-- | Since there is only one boundary, it doesn't matter if @k==First@ or
-- @k==Last@. As a result, the "name" of the boundary is kept variable.
--
-- TODO After this case we should only allow @S@, since we write, in
-- essence, left-linear grammars here.
--
-- TODO we should try to statically assure that @rb==0@ holds always in
-- this case. It should because every other symbol moves to @IVariable@
-- once the number of of reserved bits is @>0@.

instance
  ( IndexHdr s x0 i0 us (BS1 k I) cs c is (BS1 k I)
  ) => AddIndexDense s (us:.BS1 k I) (cs:.c) (is:.BS1 k I) where
  -- This rule should only be active if we have @X -> Y@ rules. Neither @X
  -- -> Y Z@ nor @X -> e Y@ are possible in a left-linear grammar.
  addIndexDenseGo (cs:.c) (vs:.IStatic rb) (lbs:._) (ubs:._) (us:.BS1 uSet uBnd) (is:.BS1 set bnd)
    = map (\(SvS s t y') ->
        let RiBs1I (BS1 cset (Boundary to)) = getIndex (getIdx s) (Proxy :: PRI is (BS1 k I))
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
            let RiBs1I (BS1 cset (Boundary to)) = getIndex (getIdx s) (Proxy :: PRI is (BS1 k I))
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

