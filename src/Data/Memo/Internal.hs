{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE RankNTypes #-}

module Data.Memo.Internal
  ( Memo(memo), memo2, memo3
  , Memo1(memoWith), memo1
  , (~>)(untrie)
  , trie
  -- * Internal Trivia
  , GMemo(gmemo)
  , GMemo1(gmemoWith)
  , memoBits
  ) where

import Control.Arrow
import Control.Applicative
import Control.Comonad
import Control.Monad.Fix
import Control.Monad.Reader.Class
import Data.Bits
import qualified Data.ByteString as SB
import qualified Data.ByteString.Lazy as LB
import Data.Complex
import Data.Distributive
import Data.Int
import qualified Data.IntMap as IntMap
import qualified Data.IntSet as IntSet
import qualified Data.Map as Map
import Data.Maybe
import Data.Monoid
import Data.Profunctor.Unsafe
import Data.Tree
import qualified Data.Vector as V
import qualified Data.Vector.Unboxed as U
import qualified Data.Vector.Primitive as P
import qualified Data.Vector.Storable as S
import Data.Ratio
import qualified Data.Set as Set
import Data.Void
import Data.Word
import qualified Data.Text as ST
import qualified Data.Text.Lazy as LT
import GHC.Generics
import Linear.V
import Linear.V2
import Linear.V3
import Linear.V4
import Linear.Plucker
import Linear.Quaternion

-- orphans

deriving instance Generic1 Tree
deriving instance Generic a => Generic (Tree a)

-- * Generic memoization

class GMemo f where
  gmemo :: (f x -> b) -> f x -> b

instance GMemo U1 where
  gmemo f = \ U1 -> m where
    m = f U1

instance GMemo V1 where
  gmemo f !x = f x -- uninhabited, so force the user's _|_

instance GMemo f => GMemo (M1 i c f) where
  gmemo f = gmemo (f .# M1) .# unM1

instance Memo a => GMemo (K1 i a) where
  gmemo f = memo (f .# K1) .# unK1

instance (GMemo f, GMemo g) => GMemo (f :+: g) where
  gmemo f = \lr -> case lr of
    L1 x -> l x
    R1 x -> r x
    where
      l = gmemo (f . L1)
      r = gmemo (f . R1)

instance (GMemo f, GMemo g) => GMemo (f :*: g) where
  gmemo f = \ (a :*: b) -> m a b where
    m = gmemo $ \a -> gmemo $ \b -> f (a :*: b)

instance GMemo f => GMemo (Rec1 f) where
  gmemo f = gmemo (f . Rec1) . unRec1

instance (Memo1 f, GMemo g) => GMemo (f :.: g) where
  gmemo f = memoWith gmemo (f . Comp1) . unComp1

class GMemo1 f where
  gmemoWith :: (forall c. (x -> c) -> x -> c) -> (f x -> b) -> f x -> b

instance GMemo1 U1 where
  gmemoWith _ = gmemo

instance GMemo1 V1 where
  gmemoWith _ = gmemo

instance GMemo1 f => GMemo1 (M1 i c f) where
  gmemoWith g f = gmemoWith g (f .# M1) .# unM1

instance Memo a => GMemo1 (K1 i a) where
  gmemoWith _ f = memo (f .# K1) .# unK1

instance (GMemo1 f, GMemo1 g) => GMemo1 (f :*: g) where
  gmemoWith g f = \ (a :*: b) -> m a b where
    m = gmemoWith g $ \a -> gmemoWith g $ \b -> f (a :*: b)

instance (GMemo1 f, GMemo1 g) => GMemo1 (f :+: g) where
  gmemoWith g f = \lr -> case lr of
    L1 x -> l x
    R1 x -> r x
    where
      l = gmemoWith g (f . L1)
      r = gmemoWith g (f . R1)

instance GMemo1 Par1 where
  gmemoWith g f = g (f . Par1) . unPar1

instance Memo1 f => GMemo1 (Rec1 f) where
  gmemoWith g f = memoWith g (f . Rec1) . unRec1

instance (Memo1 f, GMemo1 g) => GMemo1 (f :.: g) where
  gmemoWith g f = memoWith (gmemoWith g) (f . Comp1) . unComp1

-- Memoization

class Memo a where
  memo :: (a -> b) -> a -> b
  default memo :: (Generic a, GMemo (Rep a)) => (a -> b) -> a -> b
  memo f = gmemo (f . to) . from

class Memo1 f where
  memoWith :: (forall c. (a -> c) -> a -> c) -> (f a -> b) -> f a -> b

  default memoWith :: (Generic1 f, GMemo1 (Rep1 f)) =>
     (forall c. (a -> c) -> a -> c) -> (f a -> b) -> f a -> b

  memoWith g f = gmemoWith g (f . to1) . from1

memo1 :: (Memo1 f, Memo a) => (f a -> b) -> f a -> b
memo1 = memoWith memo

instance Memo a => Memo (Tree a) where memo = memo1
instance Memo1 Tree

-- * Memoized structures

newtype a ~> b = Trie { untrie :: a -> b }

trie :: Memo a => (a -> b) -> a ~> b
trie f = Trie (memo f)
{-# INLINE trie #-}

instance Memo a => Functor ((~>) a) where
  fmap f (Trie g) = trie (f . g)
  a <$ _ = Trie (const a) -- skip memo

instance Memo a => Distributive ((~>) a) where
  collect f = trie . collect (untrie . f)

instance Memo a => Applicative ((~>) a) where
  pure a  = Trie (const a) -- skip memo
  Trie m <*> Trie n = trie $ \i -> m i (n i)
  m <* _ = m
  _ *> m = m

instance Memo a => Monad ((~>) a) where
  return a = Trie $ \_ -> a -- skip memo
  Trie mf >>= k = trie $ \i -> untrie (k (mf i)) i

instance Memo a => MonadReader a ((~>) a) where
  ask = Trie id -- skip memo
  local f (Trie m) = trie $ \i -> m (f i)

instance Memo a => MonadFix ((~>) a) where
  mfix f = trie $ \ r -> let a = untrie (f a) r in a

instance (Memo a, Monoid a) => Comonad ((~>) a) where
  duplicate (Trie m) = trie $ \i -> trie $ \j -> m (mappend i j)
  extract (Trie m) = m mempty

instance (Memo a, Monoid m) => Monoid (a ~> m) where
  mempty = Trie (const mempty)
  mappend (Trie m) (Trie n) = trie (mappend m n)

-- * Utility functions

memoBits :: (Num a, Bits a) => (a -> b) -> a -> b
memoBits f = memo (f . unbits) . bits where
  bits a    = testBit a <$> [0..bitSize a-1]
  unbits xs = foldr (\(a,i) r -> if a then setBit r i else r) 0 $ zip xs [0..]

memo2 :: (Memo a, Memo b) => (a -> b -> c) -> a -> b -> c
memo2 f = memo (memo . f)

memo3 :: (Memo a, Memo b, Memo c) => (a -> b -> c -> d) -> a -> b -> c -> d
memo3 f = memo (memo2 . f)

-- * Memo instances

instance Memo ()
instance Memo Bool
instance Memo Ordering
instance (Memo a, Memo b) => Memo (Either a b)
instance (Memo a, Memo b) => Memo (a, b)
instance (Memo a, Memo b, Memo c) => Memo (a,b,c)
instance (Memo a, Memo b, Memo c, Memo d) => Memo (a,b,c,d)
instance (Memo a, Memo b, Memo c, Memo d, Memo e) => Memo (a,b,c,d,e)
instance (Memo a, Memo b, Memo c, Memo d, Memo e, Memo f) => Memo (a,b,c,d,e,f)
instance Memo a => Memo [a]
instance Memo a => Memo (Maybe a)

instance Memo1 []
instance Memo1 Maybe
instance Memo a => Memo1 (Either a)
instance Memo a => Memo1 ((,) a)
instance (Memo a, Memo b) => Memo1 ((,,) a b)
instance (Memo a, Memo b, Memo c) => Memo1 ((,,,) a b c)
instance (Memo a, Memo b, Memo c, Memo d) => Memo1 ((,,,,) a b c d)

instance Memo Int where
  memo = memoBits

instance Memo Int8 where
  memo = memoBits

instance Memo Int16 where
  memo = memoBits

instance Memo Int32 where
  memo = memoBits

instance Memo Int64 where
  memo = memoBits

instance Memo Word where
  memo = memoBits

instance Memo Word8 where
  memo = memoBits

instance Memo Word16 where
  memo = memoBits

instance Memo Word32 where
  memo = memoBits

instance Memo Word64 where
  memo = memoBits

instance Memo a => Memo1 (Const a) where
  memoWith _ f = memo (f .# Const) .# getConst

instance Memo a => Memo (Const a x) where
  memo f = memo (f .# Const) .# getConst

instance Memo1 ZipList where
  memoWith g f = memoWith g (f .# ZipList) .# getZipList

instance Memo a => Memo (ZipList a) where
  memo f = memo (f .# ZipList) .# getZipList

instance Memo1 m => Memo1 (WrappedMonad m) where
  memoWith g f = memoWith g (f .# WrapMonad) .# unwrapMonad

instance Memo (m a) => Memo (WrappedMonad m a) where
  memo f = memo (f .# WrapMonad) .# unwrapMonad

instance Memo1 (a b) => Memo1 (WrappedArrow a b) where
  memoWith g f = memoWith g (f .# WrapArrow) .# unwrapArrow

instance Memo (a b c) => Memo (WrappedArrow a b c) where
  memo f = memo (f .# WrapArrow) .# unwrapArrow

instance Memo Char where
  memo f = memo (f . toEnum . unbits) . cbits where
    cbits a | i <- fromEnum a = testBit i <$> [0..20]
    unbits xs = foldr (\(a,i) r -> if a then setBit r i else r) 0 $ zip xs [0..]

instance Memo1 Sum where
  memoWith g f = g (f .# Sum) .# getSum

instance Memo a => Memo (Sum a) where
  memo f = memo (f .# Sum) .# getSum

instance Memo1 Product where
  memoWith g f = g (f .# Product) .# getProduct

instance Memo a => Memo (Product a) where
  memo f = memo (f .# Product) .# getProduct

instance Memo1 Last where
  memoWith g f = memoWith g (f .# Last) .# getLast

instance Memo a => Memo (Last a) where
  memo f = memo (f .# Last) .# getLast

instance Memo1 First where
  memoWith g f = memoWith g (f .# First) .# getFirst

instance Memo a => Memo (First a) where
  memo f = memo (f .# First) .# getFirst

instance Memo All where
  memo f = memo (f .# All) .# getAll

instance Memo Any where
  memo f = memo (f .# Any) .# getAny

instance Memo1 Dual where
  memoWith g f = g (f .# Dual) .# getDual

instance Memo a => Memo (Dual a) where
  memo f = memo (f .# Dual) .# getDual

instance (Memo a, RealFloat a) => Memo (Complex a) where
  memo f = memo (f . uncurry (:+)) . (realPart &&& imagPart)

instance (Memo a, Integral a) => Memo (Ratio a) where
  memo f = memo (f . uncurry (%)) . (numerator &&& denominator)

instance Memo SB.ByteString where
  memo f = memo (f . SB.pack) . SB.unpack

instance Memo LB.ByteString where
  memo f = memo (f . LB.pack) . LB.unpack

instance Memo ST.Text where
  memo f = memo (f . ST.pack) . ST.unpack

instance Memo LT.Text where
  memo f = memo (f . LT.pack) . LT.unpack

instance (Ord k, Memo k, Memo a) => Memo (Map.Map k a) where
  memo f = memo (f . Map.fromList) . Map.toList

instance (Ord k, Memo k) => Memo1 (Map.Map k) where
  memoWith g f = memoWith (memoWith g) (f . Map.fromList) . Map.toList

instance Memo a => Memo (IntMap.IntMap a) where
  memo f = memo (f . IntMap.fromList) . IntMap.toList

instance Memo1 IntMap.IntMap where
  memoWith g f = memoWith (memoWith g) (f . IntMap.fromList) . IntMap.toList

instance (Memo a, Ord a) => Memo (Set.Set a) where
  memo f = memo (f . Set.fromList) . Set.toList

instance Memo IntSet.IntSet where
  memo f = memo (f . IntSet.fromList) . IntSet.toList

instance Memo1 V.Vector where
  memoWith g f = memoWith g (f . V.fromList) . V.toList

instance Memo a => Memo (V.Vector a) where
  memo f = memo (f . V.fromList) . V.toList

instance (Memo a, U.Unbox a) => Memo (U.Vector a) where
  memo f = memo (f . U.fromList) . U.toList

instance (Memo a, P.Prim a) => Memo (P.Vector a) where
  memo f = memo (f . P.fromList) . P.toList

instance (Memo a, S.Storable a) => Memo (S.Vector a) where
  memo f = memo (f . S.fromList) . S.toList

instance Memo Void where
  memo f !x = f x

instance Memo1 V2
instance Memo1 V3
instance Memo1 V4
instance Memo1 Quaternion
instance Memo1 Plucker

instance Memo a => Memo (V2 a)
instance Memo a => Memo (V3 a)
instance Memo a => Memo (V4 a)
instance Memo a => Memo (Quaternion a)
instance Memo a => Memo (Plucker a)

instance Dim n => Memo1 (V n) where
  memoWith g f = memoWith g (f . fromJust . fromVector) . toVector

instance (Memo a, Dim n) => Memo (V n a) where
  memo f = memo (f . fromJust . fromVector) . toVector
