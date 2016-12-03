
module ADP.Fusion.Term.Vertex.Set2 where

import Data.Bits
import Data.Strict.Tuple
import Data.Vector.Fusion.Stream.Monadic hiding (flatten)
import Debug.Trace
import Prelude hiding (map)

import ADP.Fusion.Core
import Data.Bits.Ordered
import Data.PrimitiveArray hiding (map)

import ADP.Fusion.Core.Set
import ADP.Fusion.Term.Vertex.Type


instance
  ( TmkCtx1 m ls (Vertex v) (BS2 First Last i)
  ) => MkStream m (ls :!: Vertex v) (BS2 First Last i) where
  mkStream (ls :!: Vertex f) sv us is
    = map (\(ss,ee,ii) -> ElmVertex ee ii ss)
    . addTermStream1 (Vertex f) sv us is
    $ mkStream ls (termStaticVar (Vertex f) sv is) us (termStreamIndex (Vertex f) sv is)
  {-# Inline mkStream #-}

instance
  ( TstCtx m ts s x0 i0 is (BS2 First Last I)
  ) => TermStream m (TermSymbol ts (Vertex v)) s (is:.BS2 First Last I) where
  termStream (ts:|Vertex f) (cs:.IStatic d) (us:.BS2 ss ui uj) (is:.BS2 s i j)
    = undefined

{-
instance
  ( Monad m
  , Element    ls (BS2 First Last I)
  , MkStream m ls (BS2 First Last I)
  ) => MkStream m (ls :!: Edge e) (BS2 First Last I) where
  mkStream (ls :!: Edge f) (IStatic rp) u sij@(BS2 s i j)
    = map go . staticCheck (s==0)
    where go = undefined
    -}
  {-
    = flatten mk step $ mkStream ls (IStatic rpn) u tik
    where rpn | j >= 0    = rp
              | otherwise = rp+1
          tik | j >= 0    = BS2 (s `clearBit` (getIter j)) i undefi
              | otherwise = sij
          mk z
            | j >= 0 && popCount s >= 2 = return $ This z
            | j <  0 && popCount s >= 2 = return $ That (z,bits,maybeLsb bits)
            | popCount s <= max 1 rp    = return $ Naught
            | otherwise                 = error $ show ("Edge",s,i,j)
            where RiBs2I (BS2 zs _ zk) = getIdx z
                  bits        = s `xor` zs
          step Naught   = return Done
          step (This z)
            | popCount zs == 0 = return $ Done
            | otherwise = return $ Yield (ElmEdge (f (getIter zk) (getIter j)) (RiBs2I sij) z) Naught
            where RiBs2I (BS2 zs _ zk) = getIdx z
          step (That (z,bits,Nothing)) = return $ Done
          step (That (z,bits,Just j')) = let RiBs2I (BS2 zs _ (Iter zk)) = getIdx z
                                             tij'                        = BS2 (zs .|. bit j') (Iter zk) (Iter j')
                                         in  return $ Yield (ElmEdge (f zk j') (RiBs2I tij') z) (That (z,bits,maybeNextActive j' bits))
          {-# Inline [0] mk   #-}
          {-# Inline [0] step #-}
  {-# Inline mkStream #-}
          -}


{-
instance
  ( Monad m
  , Element ls    (BS2 First Last O)
  , MkStream m ls (BS2 First Last O)
  ) => MkStream m (ls :!: Edge f) (BS2 First Last O) where
  mkStream (ls :!: Edge f) (OStatic ()) u sij
    = map undefined
    $ mkStream ls (undefined) u sij
  {-# Inline mkStream #-}



instance
  ( Monad m
  , Element ls    (BS2 First Last C)
  , MkStream m ls (BS2 First Last C)
  ) => MkStream m (ls :!: Edge f) (BS2 First Last C) where
  mkStream (ls :!: Edge f) Complemented u sij
    = map undefined
    $ mkStream ls Complemented u sij
  {-# Inline mkStream #-}
-}

