
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
import ADP.Fusion.Core.Unit
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
            let
            in  {- traceShow (set,bnd,rb) $ -} return (SvS s t y', set `clearBit` getBoundary bnd)
          step (_, 0) = return Done
          step (SvS s t y', bits) =
            let nbnd = lsbZ bits
                nset = set `clearBit` getBoundary bnd
                bs1  = BS1 nset (Boundary nbnd)
            in  -- traceShow (Boundary nbnd == bnd,bs1) $
                return $ Yield (SvS s (t:.bs1) (y':.:RiBs1I bs1))
                               (SvS s t y', bits `clearBit` nbnd)
          {-
            let numBits = popCount set - rb
                initSet = 2 ^ numBits - 1
                initBnd = Boundary $ lsbZ initSet
                -- TODO works only if no prior bits set... (should be the
                -- case here ...)
            in  traceShow (set,bnd,rb,initSet,initBnd) $ return (SvS s t y', Just $ BS1 initSet initBnd)
          step (_, Nothing) = return Done
          step (_, Just (BS1 nset nbnd))
            | popCount nset > popCount set - rb = return Done
          step (SvS s t y', Just (curSet@(BS1 nset nbnd))) =
            let realBS = applyMask maskSet $ curSet
            in  traceShow (nbnd == bnd,BS1 nset nbnd) $
                return $ Yield (SvS s (t:.realBS) (y':.:RiBs1I realBS))
                               (SvS s t y', setSucc (BS1 0 (-1)) (BS1 fullSet (-1)) (BS1 nset nbnd))
          fullSet = 2 ^ popCount set - 1
          maskSet = set `clearBit` getBoundary bnd
          -}
          {-
            let RiBs1I (BS1 cset (Boundary to)) = getIndex (getIdx s) (Proxy :: PRI is (BS1 k I))
                numBits = popCount cset
                stopAt  = numBits - rb + 1
                -- initialize to lowest set, that fullfills the
                -- constraints. The @Boundary@ bit is not a valid bit to
                -- set here!
                initSet  = popShiftL initMask $ 2 ^ (popCount set - rb - numBits) - 1
                initBnd  = Boundary $ lsbZ initSet
            in  assert (numBits == 0 && to == (-1) && rb > 0)
                $ traceShow (set,bnd,rb,BS1 initSet initBnd) $ return (SvS s t y', if rb > popCount set then Nothing else Just $ BS1 initSet initBnd)
          step (_, Nothing)
            = return Done
          -- TODO @setSucc@ needs to be refined to only produce valid next
          -- sets. 
          step (SvS s t y', Just (BS1 nset nbnd))
            | nbnd == bnd = return $ Skip ( SvS s t y', setSucc (BS1 0 (-1)) (BS1 initMask initBnd) (BS1 nset nbnd))
          step (SvS s t y', Just (BS1 nset nbnd)) =
            -- No need to provide @nset .|. getIndex s@ because no bit is
            -- set in @getIndex s@.
            traceShow (nbnd == bnd,BS1 nset nbnd) $ return $ Yield (SvS s (t:.BS1 nset nbnd) (y':.:RiBs1I (BS1 nset nbnd)))
                            -- TODO @setSucc@ doesn't handle the mask
                            -- correctly
                           ( SvS s t y', setSucc (BS1 0 (-1)) (BS1 initMask initBnd) (BS1 nset nbnd))
          initMask = set `clearBit` getBoundary bnd -- one less bit than @set@ has
          initBnd  = Boundary $ lsbZ initMask
          -}
          {-# Inline [0] mk       #-}
          {-# Inline [0] step     #-}
--          {-# Inline     initMask #-}
  {-# Inline addIndexDenseGo #-}

-- | A @Unit@ index expands to the full set with all possible boundaries
-- tried in order.

instance
  ( IndexHdr s x0 i0 us (BS1 k I) cs c is (Unit I)
  ) => AddIndexDense s (us:.BS1 k I) (cs:.c) (is:.Unit I) where
  addIndexDenseGo (cs:.c) (vs:.IStatic ()) (lbs:._) (ubs:.BS1 fullSet _) (us:._) (is:._) -- unit has only one index value
    = flatten mk step . addIndexDenseGo cs vs lbs ubs us is
    where mk (SvS s t y') = return $ (SvS s t y', fullSet)
          -- no more active bits
          step (_, 0) = return Done
          step (SvS s t y', bits)
            | b <- lsb bits = return $ Yield (SvS s (t:.BS1 fullSet (Boundary b)) (y':.:RiU))
                                             (SvS s t y', bits `clearBit` b)
          {-# Inline [0] mk   #-}
          {-# Inline [0] step #-}
  {-# Inline addIndexDenseGo #-}

-- | A single @Boundary@ index allows us to get the optimal results ending
-- on each individual boundary.

instance
  ( IndexHdr s x0 i0 us (BS1 k I) cs c is (Boundary I)
  ) => AddIndexDense s (us:.BS1 k I) (cs:.c) (is:.Boundary I) where
  addIndexDenseGo (cs:.c) (vs:.IStatic ()) (lbs:._) (ubs:.BS1 fullSet _) (us:._) (is:.Boundary i)
    = map (\(SvS s t y') -> undefined)
    . addIndexDenseGo cs vs lbs ubs us is
  {-# Inline addIndexDenseGo #-}

