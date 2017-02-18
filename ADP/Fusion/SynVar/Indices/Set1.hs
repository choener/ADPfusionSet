
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

import ADP.Fusion.Core.Boundary
import ADP.Fusion.Core.EdgeBoundary
import ADP.Fusion.Core.Set1



-- | Since there is only one boundary, it doesn't matter if @k==First@ or
-- @k==Last@. As a result, the "name" of the boundary is kept variable.
--
-- Given the outer (set,bnd) system, we try all boundaries α for
-- (set-bnd,α) for the smaller set @Y@ in @X -> Y e@.
--
-- TODO After this case we should only allow @S@, since we write, in
-- essence, left-linear grammars here.
--
-- TODO we should try to statically assure that @rb==0@ holds always in
-- this case. It should because every other symbol moves to @IVariable@
-- once the number of of reserved bits is @>0@.
--
-- TODO kind-of hacked and should be written in a better way

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
    = flatten mk step . addIndexDenseGo cs vs lbs ubs us is . assert (rb==1) -- only works with one element
          -- Extract how many bits are already set -- should be zero (!) --
          -- and prepare the list of all possibilities.
          -- In addition, at least one bit should be reserved, hence
          -- @rb>0@. The boundary bit is one of those reserved and
          -- constitutes a mask to be used further down.
    where mk (SvS s t y') =
            let
            in  
#if ADPFUSION_DEBUGOUTPUT
                traceShow (set,bnd,rb) $
#endif
                return (SvS s t y', Just $ set `clearBit` getBoundary bnd)
          step (_, Nothing) = return Done
          step (SvS s t y', Just 0 ) = return $ Yield (SvS s (t:.BS1 0 0) (y':.:RiBs1I (BS1 0 0)))
                                                      (SvS s t y', Nothing)
          step (SvS s t y', Just bits) =
            let nbnd = lsbZ bits
                nset = set `clearBit` getBoundary bnd
                bs1  = BS1 nset (Boundary nbnd)
            in  -- traceShow (Boundary nbnd == bnd,bs1) $
                return $ Yield (SvS s (t:.bs1) (y':.:RiBs1I bs1))
                               (SvS s t y', Just $ bits `clearBit` nbnd)
          {-# Inline [0] mk       #-}
          {-# Inline [0] step     #-}
  {-# Inline addIndexDenseGo #-}

-- | For the inside case, we try all possible boundaries for @Y@ in @X ->
-- Y e@. For the outside case we now have: @Y -> X e@ where @Y@ is now
-- extended. @(yset,ybnd) -> (yset + α,α)@ for all @α@ that are not in
-- @yset@.
--
-- TODO 17.2.2017 added

instance
  ( IndexHdr s x0 i0 us (BS1 k O) cs c is (BS1 k O)
  ) => AddIndexDense s (us:.BS1 k O) (cs:.c) (is:.BS1 k O) where
  addIndexDenseGo (cs:.c) (vs:.ORightOf rb) (lbs:._) (ubs:._) (us:.BS1 uSet uBnd) (is:.BS1 cSet cBnd)
    = flatten mk step . addIndexDenseGo cs vs lbs ubs us is . assert (rb==1) -- only works with one element to the right
          -- Extract how many bits are already set -- should be zero (!) --
          -- and prepare the list of all possibilities.
          -- In addition, at least one bit should be reserved, hence
          -- @rb>0@. The boundary bit is one of those reserved and
          -- constitutes a mask to be used further down.
    where mk (SvS s t y') =
            let possible = uSet .&. complement cSet
            in
#if ADPFUSION_DEBUGOUTPUT
                traceShow ("aIDG/BS1/O/mk",(BS1 uSet uBnd), (BS1 cSet cBnd), possible) $
#endif
                return (SvS s t y', possible)
          -- in this case, the current set does not yield something to
          -- "make smaller".
          step (_, k) | popCount uSet == popCount cSet = return Done
          -- exhausted all options
          step (_, 0) = return Done
          step (SvS s t y', bits) =
            let nbnd = lsbZ bits
                nset = cSet `setBit` nbnd
                bs1  = BS1 nset (Boundary nbnd)
            in
#if ADPFUSION_DEBUGOUTPUT
                traceShow ("aIDG/BS1/O/step",(BS1 nset (Boundary nbnd))) $
#endif
                return $ Yield (SvS s (t:.bs1) (y':.:RiBs1O bs1))
                               (SvS s t y', bits `clearBit` nbnd)
          {-# Inline [0] mk       #-}
          {-# Inline [0] step     #-}
  {-# Inline addIndexDenseGo #-}


-- | 

instance
  ( IndexHdr s x0 i0 us (BS1 k I) cs c is (BS1 k O)
  ) => AddIndexDense s (us:.BS1 k I) (cs:.c) (is:.BS1 k O) where

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
  ( IndexHdr s x0 i0 us (BS1 k I) cs c is (Boundary k I)
  ) => AddIndexDense s (us:.BS1 k I) (cs:.c) (is:.Boundary k I) where
  addIndexDenseGo (cs:.c) (vs:.IStatic ()) (lbs:._) (ubs:.BS1 fullSet _) (us:._) (is:.i)
    = map (\(SvS s t y') -> SvS s (t:.BS1 fullSet i) (y':.:RiBI i))
    . addIndexDenseGo cs vs lbs ubs us is
  {-# Inline addIndexDenseGo #-}

-- | Given indices that index _only_ the current edge @First -> Last@, we
-- want to go over all possible set combinations.
--
-- The @to@ element from an edge boundary will serve as the @First@ element
-- in a rule
-- @X -> Last (from :-> to) First

instance
  ( IndexHdr s x0 i0 us (BS1 First I) cs c is (EdgeBoundary I)
  ) => AddIndexDense s (us:.BS1 First I) (cs:.c) (is:.EdgeBoundary I) where
  addIndexDenseGo (cs:.c) (vs:.IStatic k) (lbs:._) (ubs:.BS1 fullSet _) (us:._) (is:.(from :-> to))
    = map (\(SvS s t y') ->
        let RiEBI usedSet (_ :-> _) = getIndex (getIdx s) (Proxy :: PRI is (EdgeBoundary I))
            hereBits = fullSet .&. complement usedSet
            hereSet  = hereBits `setBit` to
        in  SvS s (t:.BS1 hereSet (Boundary to)) (y':.:RiEBI fullSet (from :-> to)))
    . addIndexDenseGo cs vs lbs ubs us is
  {-# Inline addIndexDenseGo #-}

-- | Generate all possible bitsets until 'fullSet' is reached. @from@ is
-- our @Last@, and @to@ may not be set.

instance
  ( IndexHdr s x0 i0 us (BS1 Last I) cs c is (EdgeBoundary I)
  ) => AddIndexDense s (us:.BS1 Last I) (cs:.c) (is:.EdgeBoundary I) where
  addIndexDenseGo (cs:.c) (vs:.IVariable rb) (lbs:._) (ubs:.BS1 fullSet _) (us:._) (is:.(from :-> to))
    = flatten mk step . addIndexDenseGo cs vs lbs ubs us is
    where mk (SvS s t y') =
            let RiEBI usedBits (_ :-> _) = getIndex (getIdx s) (Proxy :: PRI is (EdgeBoundary I))
            in  assert (usedBits == 0) . return $ (SvS s t y', Just (zeroBits :: BitSet I))
          step (_, (Nothing :: Maybe (BitSet I))) = return $ Done
          step (SvS s t y', Just cbits)
            | popCount cbits > maxCount = return $ Done
            | otherwise =
                let sbits = popShiftL shiftMask cbits
                    cset  = sbits `setBit` from
                in  return $ Yield (SvS s (t:.BS1 cset (Boundary from)) (y':.:RiEBI cset (from :-> to)))
                                   (SvS s t y', setSucc zeroBits (BitSet $ 2^maxCount-1) cbits)
          !maxCount = popCount fullSet - rb - 1 -- remove one for @from@, the @to@ bit should be in @rb@
          !shiftMask = fullSet `clearBit` from `clearBit` to
          {-# Inline [0] mk   #-}
          {-# Inline [0] step #-}
  {-# Inline addIndexDenseGo #-}

-- | TODO 17.2.2017 added

instance
  ( IndexHdr s x0 i0 us (BS1 First I) cs c is (EdgeBoundary C)
  ) => AddIndexDense s (us:.BS1 First I) (cs:.c) (is:.EdgeBoundary C) where
  addIndexDenseGo (cs:.c) (vs:.CStatic()) (lbs:._) (ubs:.BS1 (BitSet fullSet) _) (us:._) (is:.(from :-> to))
    = map (\(SvS s t y') ->
        let RiEBC (BitSet usedSet) (_ :-> _) = getIndex (getIdx s) (Proxy :: PRI is (EdgeBoundary C))
            hereBits = fullSet .&. complement usedSet
            hereSet  = hereBits `setBit` to
        in  SvS s (t:.BS1 (BitSet hereSet) (Boundary to)) (y':.:RiEBC (BitSet fullSet) (from :-> to)))
    . addIndexDenseGo cs vs lbs ubs us is
  addIndexDenseGo (cs:.c) (vs:.CVariable ()) (lbs:._) (ubs:.BS1 fullSet _) (us:._) (is:.(from :-> to))
    = flatten mk step . addIndexDenseGo cs vs lbs ubs us is
    where mk (SvS s t y') =
            let RiEBC usedBits (_ :-> _) = getIndex (getIdx s) (Proxy :: PRI is (EdgeBoundary C))
            in  assert (usedBits == 0) . return $ (SvS s t y', Just (zeroBits :: BitSet I))
          step (_, Nothing) = return $ Done
          step (SvS s t y', Just cbits)
            | popCount cbits > maxCount = return $ Done
            | otherwise =
                let sbits = popShiftL shiftMask cbits
                    cset  = getBitSet $ sbits `setBit` from
                in  return $ Yield (SvS s (t:.BS1 (BitSet cset) (Boundary from)) (y':.:RiEBC (BitSet cset) (from :-> to)))
                                   (SvS s t y', setSucc zeroBits (BitSet $ 2^maxCount-1) cbits)
          !maxCount = popCount fullSet - 1 -- remove one for @from@, the @to@ bit should be in @rb@
          !shiftMask = fullSet `clearBit` from `clearBit` to
          {-# Inline [0] mk   #-}
          {-# Inline [0] step #-}
  {-# Inline addIndexDenseGo #-}

-- | TODO 17.2.2017 added

instance
  ( IndexHdr s x0 i0 us (BS1 First O) cs c is (EdgeBoundary C)
  ) => AddIndexDense s (us:.BS1 First O) (cs:.c) (is:.EdgeBoundary C) where
  addIndexDenseGo (cs:.c) (vs:.CStatic()) (lbs:._) (ubs:.BS1 (BitSet fullSet) _) (us:._) (is:.(from :-> to))
    = map (\(SvS s t y') ->
        let RiEBC (BitSet usedSet) (_ :-> _) = getIndex (getIdx s) (Proxy :: PRI is (EdgeBoundary C))
            hereBits = fullSet .&. complement usedSet
            hereSet  = hereBits `setBit` to
        in  SvS s (t:.BS1 (BitSet hereSet) (Boundary to)) (y':.:RiEBC (BitSet fullSet) (from :-> to)))
    . addIndexDenseGo cs vs lbs ubs us is
  addIndexDenseGo (cs:.c) (vs:.CVariable ()) (lbs:._) (ubs:.BS1 fullSet _) (us:._) (is:.(from :-> to))
    = flatten mk step . addIndexDenseGo cs vs lbs ubs us is
    where mk (SvS s t y') =
            let RiEBC usedBits (_ :-> _) = getIndex (getIdx s) (Proxy :: PRI is (EdgeBoundary C))
            in  assert (usedBits == 0) . return $ (SvS s t y', Just (zeroBits :: BitSet O))
          step (_, Nothing) = return $ Done
          step (SvS s t y', Just cbits)
            | popCount cbits > maxCount = return $ Done
            | otherwise =
                let sbits = popShiftL shiftMask cbits
                    cset  = getBitSet $ sbits `setBit` from
                in  return $ Yield (SvS s (t:.BS1 (BitSet cset) (Boundary from)) (y':.:RiEBC (BitSet cset) (from :-> to)))
                                   (SvS s t y', setSucc zeroBits (BitSet $ 2^maxCount-1) cbits)
          !maxCount = popCount fullSet - 1 -- remove one for @from@, the @to@ bit should be in @rb@
          !shiftMask = fullSet `clearBit` from `clearBit` to
          {-# Inline [0] mk   #-}
          {-# Inline [0] step #-}
  {-# Inline addIndexDenseGo #-}

-- | TODO 18.2.2017 added

instance
  ( IndexHdr s x0 i0 us (BS1 Last I) cs c is (EdgeBoundary C)
  ) => AddIndexDense s (us:.BS1 Last I) (cs:.c) (is:.EdgeBoundary C) where
{-
  addIndexDenseGo (cs:.c) (vs:.CStatic()) (lbs:._) (ubs:.BS1 (BitSet fullSet) _) (us:._) (is:.(from :-> to))
    = map (\(SvS s t y') ->
        let RiEBC (BitSet usedSet) (_ :-> _) = getIndex (getIdx s) (Proxy :: PRI is (EdgeBoundary C))
            hereBits = fullSet .&. complement usedSet
            hereSet  = hereBits `setBit` to
        in  SvS s (t:.BS1 (BitSet hereSet) (Boundary to)) (y':.:RiEBC (BitSet fullSet) (from :-> to)))
    . addIndexDenseGo cs vs lbs ubs us is
    -}
  addIndexDenseGo (cs:.c) (vs:.CVariable ()) (lbs:._) (ubs:.BS1 fullSet _) (us:._) (is:.(from :-> to))
    = flatten mk step . addIndexDenseGo cs vs lbs ubs us is
    where mk (SvS s t y') =
            let RiEBC usedBits (_ :-> _) = getIndex (getIdx s) (Proxy :: PRI is (EdgeBoundary C))
            in  assert (usedBits == 0) . return $ (SvS s t y', Just (zeroBits :: BitSet I))
          step (_, Nothing) = return $ Done
          step (SvS s t y', Just cbits)
            | popCount cbits > maxCount = return $ Done
            | (zeroBits `setBit` from `setBit` to) .&. cbits > 0 =
                return $ Skip (SvS s t y', setSucc zeroBits (BitSet $ 2^maxCount-1) cbits)
            | otherwise =
                let sbits = cbits -- popShiftL shiftMask cbits
                    cset  = getBitSet $ sbits `setBit` from -- `setBit` to
                in
#if ADPFUSION_DEBUGOUTPUT
                    traceShow ("EB/BS1-Last-I/C/step",(BS1 (BitSet cset) (Boundary from))) $
#endif
                    return $ Yield (SvS s (t:.BS1 (BitSet cset) (Boundary from)) (y':.:RiEBC (BitSet cset) (from :-> to)))
                                   (SvS s t y', setSucc zeroBits (BitSet $ 2^maxCount-1) cbits)
          !maxCount = popCount fullSet - 1 -- remove one for @from@, the @to@ bit should be in @rb@
          !shiftMask = fullSet `clearBit` from `clearBit` to
          {-# Inline [0] mk   #-}
          {-# Inline [0] step #-}
  {-# Inline addIndexDenseGo #-}

-- | TODO 18.2.2017 added

instance
  ( IndexHdr s x0 i0 us (BS1 Last O) cs c is (EdgeBoundary C)
  ) => AddIndexDense s (us:.BS1 Last O) (cs:.c) (is:.EdgeBoundary C) where
  addIndexDenseGo (cs:.c) (vs:.CStatic()) (lbs:._) (ubs:.BS1 (BitSet fullSet) _) (us:._) (is:.(from :-> to))
    = map (\(SvS s t y') ->
        let RiEBC (BitSet usedSet) (_ :-> _) = getIndex (getIdx s) (Proxy :: PRI is (EdgeBoundary C))
            hereBits = usedSet -- fullSet .&. complement usedSet
            hereSet  = hereBits `setBit` to `setBit` from
        in
#if ADPFUSION_DEBUGOUTPUT
            traceShow ("EB/BS1-Last-O/C/step",(BS1 (BitSet hereSet) (Boundary to))) $
#endif
            SvS s (t:.BS1 (BitSet hereSet) (Boundary to)) (y':.:RiEBC (BitSet fullSet) (from :-> to)))
    . addIndexDenseGo cs vs lbs ubs us is
{-
  addIndexDenseGo (cs:.c) (vs:.CVariable ()) (lbs:._) (ubs:.BS1 fullSet _) (us:._) (is:.(from :-> to))
    = flatten mk step . addIndexDenseGo cs vs lbs ubs us is
    where mk (SvS s t y') =
            let RiEBC usedBits (_ :-> _) = getIndex (getIdx s) (Proxy :: PRI is (EdgeBoundary C))
            in  assert (usedBits == 0) . return $ (SvS s t y', Just (zeroBits :: BitSet O))
          step (_, Nothing) = return $ Done
          step (SvS s t y', Just cbits)
            | popCount cbits > maxCount = return $ Done
            | otherwise =
                let sbits = popShiftL shiftMask cbits
                    cset  = getBitSet $ sbits `setBit` from
                in  return $ Yield (SvS s (t:.BS1 (BitSet cset) (Boundary from)) (y':.:RiEBC (BitSet cset) (from :-> to)))
                                   (SvS s t y', setSucc zeroBits (BitSet $ 2^maxCount-1) cbits)
          !maxCount = popCount fullSet - 1 -- remove one for @from@, the @to@ bit should be in @rb@
          !shiftMask = fullSet `clearBit` from `clearBit` to
          {-# Inline [0] mk   #-}
          {-# Inline [0] step #-}
-}
  {-# Inline addIndexDenseGo #-}

