
{-# Options_GHC -O0 #-}

module QuickCheck.Set where

import           Data.Bits
import           Data.Bits.Extras (msb)
import           Data.Vector.Fusion.Util
import           Debug.Trace
import qualified Data.List as L
import qualified Data.Vector.Fusion.Stream.Monadic as SM
import qualified Data.Vector.Unboxed as VU
import           Test.QuickCheck.All
import           Test.QuickCheck hiding (NonEmpty)
import           Test.QuickCheck.Monadic
#ifdef ADPFUSION_TEST_SUITE_PROPERTIES
import           Test.Framework.TH
import           Test.Framework.Providers.QuickCheck2
#endif

import           Data.Bits.Ordered
import           Data.PrimitiveArray

import           ADP.Fusion



-- * BitSets without interfaces

-- ** Inside checks

prop_BS0_I_Eps ix@(BitSet _) = zs == ls where
  zs = (id <<< Epsilon ... stoList) highestBi ix
  ls = [ () | ix == 0 ]

prop_BS0_I_Iv ix@(BitSet _) = {- traceShow (zs,ls) $ -} L.sort zs == L.sort ls where
  tia = ITbl 0 0 EmptyOk xsB (\ _ _ -> Id 1)
  zs = ((,) <<< tia % chr csB0 ... stoList) highestBi ix
  ls = [ (xsB ! (clearBit ix a), csB0 VU.! a) | a <- activeBitsL ix ]

prop_BS0_I_Ivv ix@(BitSet _) = {- traceShow (zs,ls) $ -} L.sort zs == L.sort ls where
  tia = ITbl 0 0 EmptyOk xsB (\ _ _ -> Id 1)
  zs = ((,,) <<< tia % chr csB0 % chr csB0 ... stoList) highestBi ix
  ls = [ (xsB ! (clearBit (clearBit ix a) b), csB0 VU.! a, csB0 VU.! b) | a <- activeBitsL ix, b <- activeBitsL ix, a /=b ]

prop_BS0_I_II ix@(BitSet _) = zs == ls where
  tia = ITbl 0 0 EmptyOk xsB (\ _ _ -> Id 1)
  tib = ITbl 0 0 EmptyOk xsB (\ _ _ -> Id 1)
  zs = ((,) <<< tia % tib ... stoList) highestBi ix
  ls = [ ( xsB ! kk , xsB ! (ix `xor` kk) )
       | k <- VU.toList . popCntSorted $ popCount ix -- [ 0 .. 2^(popCount ix) -1 ]
       , let kk = popShiftL ix (BitSet k)
       ]

prop_BS0_I_JJ ix@(BitSet _) = zs == ls where
  tia = ITbl 0 0 NonEmpty xsB (\ _ _ -> Id 1)
  tib = ITbl 0 0 NonEmpty xsB (\ _ _ -> Id 1)
  zs = ((,) <<< tia % tib ... stoList) highestBi ix
  ls = [ ( xsB ! kk , xsB ! (ix `xor` kk) )
       | k <- VU.toList . popCntSorted $ popCount ix -- [ 0 .. 2^(popCount ix) -1 ]
       , let kk = popShiftL ix (BitSet k)
       , popCount kk > 0
       , popCount (ix `xor` kk) > 0
       ]

prop_BS0_I_III ix@(BitSet _) = {- traceShow (zs,ls) $ -} zs == ls where
  tia = ITbl 0 0 EmptyOk xsB (\ _ _ -> Id 1)
  tib = ITbl 0 0 EmptyOk xsB (\ _ _ -> Id 1)
  tic = ITbl 0 0 EmptyOk xsB (\ _ _ -> Id 1)
  zs = ((,,) <<< tia % tib % tic ... stoList) highestBi ix
  ls = [ ( xsB ! kk , xsB ! ll , xsB ! mm )
       | k <- VU.toList . popCntSorted $ popCount ix
       , l <- VU.toList . popCntSorted $ popCount ix - popCount k
       , let kk = popShiftL ix          (BitSet k)
       , let ll = popShiftL (ix `xor` kk) (BitSet l)
       , let mm = (ix `xor` (kk .|. ll))
       ]

prop_BS0_I_JJJ ix@(BitSet _) = zs == ls where
  tia = ITbl 0 0 NonEmpty xsB (\ _ _ -> Id 1)
  tib = ITbl 0 0 NonEmpty xsB (\ _ _ -> Id 1)
  tic = ITbl 0 0 NonEmpty xsB (\ _ _ -> Id 1)
  zs = ((,,) <<< tia % tib % tic ... stoList) highestBi ix
  ls = [ ( xsB ! kk , xsB ! ll , xsB ! mm )
       | k <- VU.toList . popCntSorted $ popCount ix
       , l <- VU.toList . popCntSorted $ popCount ix - popCount k
       , let kk = popShiftL ix          (BitSet k)
       , let ll = popShiftL (ix `xor` kk) (BitSet l)
       , let mm = (ix `xor` (kk .|. ll))
       , popCount kk > 0, popCount ll > 0, popCount mm > 0
       ]


-- * Outside checks
-- These checks are very similar to those in the @Subword@ module. We just
-- need to be a bit more careful, as indexed sets have overlap.

prop_BS0_O_Eps ix@(BitSet _) = zs == ls where
  zs = (id <<< Epsilon ... stoList) highestBo ix
  ls = [ () | ix == highestBo ]

prop_BS0_O_O ix@(BitSet _) = zs == ls where
  tia = ITbl 0 0 EmptyOk xoB (\ _ _ -> Id 1)
  zs = (id <<< tia ... stoList) highestBo ix
  ls = [ xoB ! ix ]

--prop_BS0_O_IO ix@(BitSet _) = zs == ls where
--  tia = ITbl 0 0 EmptyOk xsB (\ _ _ -> Id 1)
--  tib = ITbl 0 0 EmptyOk xoB (\ _ _ -> Id 1)
--  zs = ((,) <<< tia % tib ... stoList) highestBo ix
--  ls = []
--  {-
--  ls = [ ( xsB ! kk , xsB ! (ix `xor` kk) )
--       | k <- VU.toList . popCntSorted $ popCount ix -- [ 0 .. 2^(popCount ix) -1 ]
--       , let kk = popShiftL ix (BitSet k)
--       ] -}

{-
prop_BS0_I_II ix@(BitSet _) = zs == ls where
  tia = ITbl 0 0 EmptyOk xsB (\ _ _ -> Id 1)
  tib = ITbl 0 0 EmptyOk xsB (\ _ _ -> Id 1)
  zs = ((,) <<< tia % tib ... stoList) highestBi ix
  ls = [ ( xsB ! kk , xsB ! (ix `xor` kk) )
       | k <- VU.toList . popCntSorted $ popCount ix -- [ 0 .. 2^(popCount ix) -1 ]
       , let kk = popShiftL ix (BitSet k)
       ]
-}


-- ** Two non-terminals.
--
-- @A_s -> B_(s\t) C_t    (s\t) ++ t == s@
-- @s = 111 , s\t = 101, t = 010@
--
-- with @Z@ the full set.
-- @Z = 1111@

-- @B*_Z\(s\t) -> A*_Z\s C_t@
-- @Z\(s\t) = 1010, Z\s = 1000, t = 010@




-- * BitSets with two interfaces

-- ** Inside checks

--prop_bii_i :: BS2 First Last I -> Bool
--prop_bii_i ix@(BS2 s i j) = zs == ls where
--  tia = ITbl 0 0 EmptyOk xsBII (\ _ _ -> Id 1)
--  zs = (id <<< tia ... stoList) highestBII ix
--  ls = [ xsBII ! ix ]
--
--prop_bii_i_n :: BS2 First Last I -> Bool
--prop_bii_i_n ix@(BS2 s i j) = zs == ls where
--  tia = ITbl 0 0 NonEmpty xsBII (\ _ _ -> Id 1)
--  zs = (id <<< tia ... stoList) highestBII ix
--  ls = [ xsBII ! ix | popCount s > 0 ]

-- | Edges should never work as a single terminal element.

--prop_bii_e :: BS2 First Last I -> Bool
--prop_bii_e ix@(BS2 s (Iter i) (Iter j)) = zs == ls where
--  e   = Edge (\ i j -> (i,j)) :: Edge (Int,Int)
--  zs = (id <<< e ... stoList) highestBII ix
--  ls = [] :: [ (Int,Int) ]

-- | Edges extend only in cases where in @i -> j@, @i@ actually happens to
-- be a true interface.

--prop_bii_ie :: BS2 First Last I -> Bool
--prop_bii_ie ix@(BS2 s i (Iter j)) = zs == ls where
--  tia = ITbl 0 0 EmptyOk xsBII (\ _ _ -> Id 1)
--  e   = Edge (\ i j -> (i,j)) :: Edge (Int,Int)
--  zs = ((,) <<< tia % e ... stoList) highestBII ix
--  ls = [ ( xsBII ! (BS2 t i (Iter k :: Interface Last)) , (k,j) )
--       | let t = s `clearBit` j
--       , k <- activeBitsL t ]
--
--prop_bii_ie_n :: BS2 First Last I -> Bool
--prop_bii_ie_n ix@(BS2 s i (Iter j)) = zs == ls where
--  tia = ITbl 0 0 NonEmpty xsBII (\ _ _ -> Id 1)
--  e   = Edge (\ i j -> (i,j)) :: Edge (Int,Int)
--  zs = ((,) <<< tia % e ... stoList) highestBII ix
--  ls = [ ( xsBII ! (BS2 t i (Iter k :: Interface Last)) , (k,j) )
--       | let t = s `clearBit` j
--       , popCount t >= 2
--       , k <- activeBitsL t
--       , k /= getIter i
--       ]
--
--prop_bii_iee :: BS2 First Last I -> Bool
--prop_bii_iee ix@(BS2 s i (Iter j)) = L.sort zs == L.sort ls where
--  tia = ITbl 0 0 EmptyOk xsBII (\ _ _ -> Id 1)
--  e   = Edge (\ i j -> (i,j)) :: Edge (Int,Int)
--  zs = ((,,) <<< tia % e % e ... stoList) highestBII ix
--  ls = [ ( xsBII ! (BS2 t i kk) , (k,l) , (l,j) )
--       | let tmp = (s `clearBit` j)
--       , l <- activeBitsL tmp
--       , l /= getIter i
--       , let t = tmp `clearBit` l
--       , k <- activeBitsL t
--       , let kk = Iter k
--       ]
--
--prop_bii_ieee :: BS2 First Last I -> Bool
--prop_bii_ieee ix@(BS2 s i (Iter j)) = L.sort zs == L.sort ls where
--  tia = ITbl 0 0 EmptyOk xsBII (\ _ _ -> Id 1)
--  e   = Edge (\ i j -> (i,j)) :: Edge (Int,Int)
--  zs = ((,,,) <<< tia % e % e % e ... stoList) highestBII ix
--  ls = [ ( xsBII ! (BS2 t i kk) , (k,l) , (l,m) , (m,j) )
--       | let tmpM = (s `clearBit` j)
--       , m <- activeBitsL tmpM
--       , m /= getIter i
--       , let tmpL = (tmpM `clearBit` m)
--       , l <- activeBitsL tmpL
--       , l /= getIter i
--       , let t = tmpL `clearBit` l
--       , k <- activeBitsL t
--       , let kk = Iter k
--       ]
--
--prop_bii_iee_n :: BS2 First Last I -> Bool
--prop_bii_iee_n ix@(BS2 s i (Iter j)) = L.sort zs == L.sort ls where
--  tia = ITbl 0 0 NonEmpty xsBII (\ _ _ -> Id 1)
--  e   = Edge (\ i j -> (i,j)) :: Edge (Int,Int)
--  zs = ((,,) <<< tia % e % e ... stoList) highestBII ix
--  ls = [ ( xsBII ! (BS2 t i kk) , (k,l) , (l,j) )
--       | let tmp = (s `clearBit` j)
--       , l <- activeBitsL tmp
--       , l /= getIter i
--       , let t = tmp `clearBit` l
--       , popCount t >= 2
--       , k <- activeBitsL t
--       , k /= getIter i
--       , let kk = Iter k
--       ]
--
--prop_bii_ieee_n :: BS2 First Last I -> Bool
--prop_bii_ieee_n ix@(BS2 s i (Iter j)) = L.sort zs == L.sort ls where
--  tia = ITbl 0 0 NonEmpty xsBII (\ _ _ -> Id 1)
--  e   = Edge (\ i j -> (i,j)) :: Edge (Int,Int)
--  zs = ((,,,) <<< tia % e % e % e ... stoList) highestBII ix
--  ls = [ ( xsBII ! (BS2 t i kk) , (k,l) , (l,m) , (m,j) )
--       | let tmpM = (s `clearBit` j)
--       , m <- activeBitsL tmpM
--       , m /= getIter i
--       , let tmpL = (tmpM `clearBit` m)
--       , l <- activeBitsL tmpL
--       , l /= getIter i
--       , let t = tmpL `clearBit` l
--       , popCount t >= 2
--       , k <- activeBitsL t
--       , k /= getIter i
--       , let kk = Iter k
--       ]

-- prop_bii_ii (ix@(s:>i:>j) :: (BitSet:>Interface First:>Interface Last)) = tr zs ls $ zs == ls where
--   tia = ITbl 0 0 EmptyOk xsBII (\ _ _ -> Id 1)
--   tib = ITbl 0 0 EmptyOk xsBII (\ _ _ -> Id 1)
--   zs = ((,) <<< tia % tib ... stoList) highestBII ix
--   ls = [ ( xsBII ! kk , xsBII ! ll )
--        | k  <- VU.toList . popCntSorted $ popCount s
--        , ki <- if k==0 then [0] else activeBitsL k
--        , kj <- if | k==0 -> [0] | popCount k==1 -> [ki] | otherwise -> activeBitsL (k `clearBit` ki)
--        , let kk = (BitSet k:>Iter ki:>Iter kj)
--        , let l  = s `xor` BitSet k
--        , li <- if l==0 then [0] else activeBitsL l
--        , lj <- if | l==0 -> [0] | popCount l==1 -> [li] | otherwise -> activeBitsL (l `clearBit` li)
--        , let ll = (l:>Iter li:>Iter lj)
--        ]



-- * Helper functions

stoList = unId . SM.toList

highBit = fromIntegral arbitraryBitSetMax -- should be the same as the highest bit in Index.Set.arbitrary
highestBi :: BitSet I
highestBi = BitSet $ 2^(highBit+1) -1
highestBo :: BitSet O
highestBo = BitSet $ 2^(highBit+1) -1
highestBII = BS2 highestBi (Iter $ highBit-1) (Iter $ highBit-1) -- assuming @highBit >= 1@

xsB :: Unboxed (BitSet I) Int
xsB = fromList (BitSet 0) highestBi [ 0 .. ]

xoB :: Unboxed (BitSet O) Int
xoB = fromList (BitSet 0) highestBo [ 0 .. ]

xsBII :: Unboxed (BS2 First Last I) Int
xsBII = fromList (BS2 0 0 0) highestBII [ 0 .. ]

csB0 :: VU.Vector Int
csB0 = VU.fromList [ i | i <- [0 .. msb highestBi] ]

-- * general quickcheck stuff

options = stdArgs {maxSuccess = 1000}

customCheck = quickCheckWithResult options

return []
allProps = $forAllProperties customCheck



#ifdef ADPFUSION_TEST_SUITE_PROPERTIES
testgroup_set = $(testGroupGenerator)
#endif


