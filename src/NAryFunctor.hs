{-# LANGUAGE RankNTypes, TypeFamilies, TypeFamilyDependencies, TypeInType #-}
module NAryFunctor where

import Data.Kind
import Data.Functor.Identity


newtype NMap1 k (f :: Type -> k) (f' :: Type -> k) = NMap1
  { (<#>) :: forall a b. (a -> b) -> NMap k (f a) (f' b)
  }

type family NMap k = (r :: k -> k -> Type) | r -> k where
  NMap Type        = (->)
  NMap (Type -> k) = NMap1 k

class NFunctor (f :: k) where
  nmap :: NMap k f f


-- |
-- >>> nmap (42 :: Int)
-- 42
instance NFunctor Int where
  nmap = id

-- |
-- >>> nmap <#> (+1) $ (Identity 0 :: Identity Int)
-- Identity 1
instance NFunctor Identity where
  nmap = NMap1 $ \f1
      -> \(Identity x1)
      -> Identity (f1 x1)


-- |
-- >>> nmap <#> (+1) <#> (+2) $ (0::Int, 0::Int)
-- (1,2)
instance NFunctor (,) where
  nmap = NMap1 $ \f1
      -> NMap1 $ \f2
      -> \(x1,x2)
      -> (f1 x1, f2 x2)

-- |
-- >>> nmap <#> (+1) <#> (+2) <#> (+3) $ (0::Int, 0::Int, 0::Int)
-- (1,2,3)
instance NFunctor (,,) where
  nmap = NMap1 $ \f1
      -> NMap1 $ \f2
      -> NMap1 $ \f3
      -> \(x1,x2,x3)
      -> (f1 x1, f2 x2, f3 x3)

-- |
-- >>> nmap <#> (+1) <#> (+2) <#> (+3) <#> (+4) $ (0::Int, 0::Int, 0::Int, 0::Int)
-- (1,2,3,4)
instance NFunctor (,,,) where
  nmap = NMap1 $ \f1
      -> NMap1 $ \f2
      -> NMap1 $ \f3
      -> NMap1 $ \f4
      -> \(x1,x2,x3,x4)
      -> (f1 x1, f2 x2, f3 x3, f4 x4)

-- |
-- >>> nmap <#> (+1) <#> (+2) <#> (+3) <#> (+4) <#> (+5) $ (0::Int, 0::Int, 0::Int, 0::Int, 0::Int)
-- (1,2,3,4,5)
instance NFunctor (,,,,) where
  nmap = NMap1 $ \f1
      -> NMap1 $ \f2
      -> NMap1 $ \f3
      -> NMap1 $ \f4
      -> NMap1 $ \f5
      -> \(x1,x2,x3,x4,x5)
      -> (f1 x1, f2 x2, f3 x3, f4 x4, f5 x5)

-- |
-- >>> nmap <#> (+1) <#> (+2) <#> (+3) <#> (+4) <#> (+5) <#> (+6) $ (0::Int, 0::Int, 0::Int, 0::Int, 0::Int, 0::Int)
-- (1,2,3,4,5,6)
instance NFunctor (,,,,,) where
  nmap = NMap1 $ \f1
      -> NMap1 $ \f2
      -> NMap1 $ \f3
      -> NMap1 $ \f4
      -> NMap1 $ \f5
      -> NMap1 $ \f6
      -> \(x1,x2,x3,x4,x5,x6)
      -> (f1 x1, f2 x2, f3 x3, f4 x4, f5 x5, f6 x6)

-- |
-- >>> nmap <#> (+1) <#> (+2) <#> (+3) <#> (+4) <#> (+5) <#> (+6) <#> (+7) $ (0::Int, 0::Int, 0::Int, 0::Int, 0::Int, 0::Int, 0::Int)
-- (1,2,3,4,5,6,7)
instance NFunctor (,,,,,,) where
  nmap = NMap1 $ \f1
      -> NMap1 $ \f2
      -> NMap1 $ \f3
      -> NMap1 $ \f4
      -> NMap1 $ \f5
      -> NMap1 $ \f6
      -> NMap1 $ \f7
      -> \(x1,x2,x3,x4,x5,x6,x7)
      -> (f1 x1, f2 x2, f3 x3, f4 x4, f5 x5, f6 x6, f7 x7)

-- |
-- >>> nmap <#> (+1) <#> (+2) <#> (+3) <#> (+4) <#> (+5) <#> (+6) <#> (+7) <#> (+8) $ (0::Int, 0::Int, 0::Int, 0::Int, 0::Int, 0::Int, 0::Int, 0::Int)
-- (1,2,3,4,5,6,7,8)
instance NFunctor (,,,,,,,) where
  nmap = NMap1 $ \f1
      -> NMap1 $ \f2
      -> NMap1 $ \f3
      -> NMap1 $ \f4
      -> NMap1 $ \f5
      -> NMap1 $ \f6
      -> NMap1 $ \f7
      -> NMap1 $ \f8
      -> \(x1,x2,x3,x4,x5,x6,x7,x8)
      -> (f1 x1, f2 x2, f3 x3, f4 x4, f5 x5, f6 x6, f7 x7, f8 x8)

-- |
-- >>> nmap <#> (+1) <#> (+2) <#> (+3) <#> (+4) <#> (+5) <#> (+6) <#> (+7) <#> (+8) <#> (+9) $ (0::Int, 0::Int, 0::Int, 0::Int, 0::Int, 0::Int, 0::Int, 0::Int, 0::Int)
-- (1,2,3,4,5,6,7,8,9)
instance NFunctor (,,,,,,,,) where
  nmap = NMap1 $ \f1
      -> NMap1 $ \f2
      -> NMap1 $ \f3
      -> NMap1 $ \f4
      -> NMap1 $ \f5
      -> NMap1 $ \f6
      -> NMap1 $ \f7
      -> NMap1 $ \f8
      -> NMap1 $ \f9
      -> \(x1,x2,x3,x4,x5,x6,x7,x8,x9)
      -> (f1 x1, f2 x2, f3 x3, f4 x4, f5 x5, f6 x6, f7 x7, f8 x8, f9 x9)

-- |
-- >>> nmap <#> (+1) <#> (+2) <#> (+3) <#> (+4) <#> (+5) <#> (+6) <#> (+7) <#> (+8) <#> (+9) <#> (+10) $ (0::Int, 0::Int, 0::Int, 0::Int, 0::Int, 0::Int, 0::Int, 0::Int, 0::Int, 0::Int)
-- (1,2,3,4,5,6,7,8,9,10)
instance NFunctor (,,,,,,,,,) where
  nmap = NMap1 $ \f1
      -> NMap1 $ \f2
      -> NMap1 $ \f3
      -> NMap1 $ \f4
      -> NMap1 $ \f5
      -> NMap1 $ \f6
      -> NMap1 $ \f7
      -> NMap1 $ \f8
      -> NMap1 $ \f9
      -> NMap1 $ \f10
      -> \(x1,x2,x3,x4,x5,x6,x7,x8,x9,x10)
      -> (f1 x1, f2 x2, f3 x3, f4 x4, f5 x5, f6 x6, f7 x7, f8 x8, f9 x9, f10 x10)

-- |
-- >>> nmap <#> (+1) <#> (+2) <#> (+3) <#> (+4) <#> (+5) <#> (+6) <#> (+7) <#> (+8) <#> (+9) <#> (+10) <#> (+11) $ (0::Int, 0::Int, 0::Int, 0::Int, 0::Int, 0::Int, 0::Int, 0::Int, 0::Int, 0::Int, 0::Int)
-- (1,2,3,4,5,6,7,8,9,10,11)
instance NFunctor (,,,,,,,,,,) where
  nmap = NMap1 $ \f1
      -> NMap1 $ \f2
      -> NMap1 $ \f3
      -> NMap1 $ \f4
      -> NMap1 $ \f5
      -> NMap1 $ \f6
      -> NMap1 $ \f7
      -> NMap1 $ \f8
      -> NMap1 $ \f9
      -> NMap1 $ \f10
      -> NMap1 $ \f11
      -> \(x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11)
      -> (f1 x1, f2 x2, f3 x3, f4 x4, f5 x5, f6 x6, f7 x7, f8 x8, f9 x9, f10 x10, f11 x11)

-- |
-- >>> nmap <#> (+1) <#> (+2) <#> (+3) <#> (+4) <#> (+5) <#> (+6) <#> (+7) <#> (+8) <#> (+9) <#> (+10) <#> (+11) <#> (+12) $ (0::Int, 0::Int, 0::Int, 0::Int, 0::Int, 0::Int, 0::Int, 0::Int, 0::Int, 0::Int, 0::Int, 0::Int)
-- (1,2,3,4,5,6,7,8,9,10,11,12)
instance NFunctor (,,,,,,,,,,,) where
  nmap = NMap1 $ \f1
      -> NMap1 $ \f2
      -> NMap1 $ \f3
      -> NMap1 $ \f4
      -> NMap1 $ \f5
      -> NMap1 $ \f6
      -> NMap1 $ \f7
      -> NMap1 $ \f8
      -> NMap1 $ \f9
      -> NMap1 $ \f10
      -> NMap1 $ \f11
      -> NMap1 $ \f12
      -> \(x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12)
      -> (f1 x1, f2 x2, f3 x3, f4 x4, f5 x5, f6 x6, f7 x7, f8 x8, f9 x9, f10 x10, f11 x11, f12 x12)

-- |
-- >>> nmap <#> (+1) <#> (+2) <#> (+3) <#> (+4) <#> (+5) <#> (+6) <#> (+7) <#> (+8) <#> (+9) <#> (+10) <#> (+11) <#> (+12) <#> (+13) $ (0::Int, 0::Int, 0::Int, 0::Int, 0::Int, 0::Int, 0::Int, 0::Int, 0::Int, 0::Int, 0::Int, 0::Int, 0::Int)
-- (1,2,3,4,5,6,7,8,9,10,11,12,13)
instance NFunctor (,,,,,,,,,,,,) where
  nmap = NMap1 $ \f1
      -> NMap1 $ \f2
      -> NMap1 $ \f3
      -> NMap1 $ \f4
      -> NMap1 $ \f5
      -> NMap1 $ \f6
      -> NMap1 $ \f7
      -> NMap1 $ \f8
      -> NMap1 $ \f9
      -> NMap1 $ \f10
      -> NMap1 $ \f11
      -> NMap1 $ \f12
      -> NMap1 $ \f13
      -> \(x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13)
      -> (f1 x1, f2 x2, f3 x3, f4 x4, f5 x5, f6 x6, f7 x7, f8 x8, f9 x9, f10 x10, f11 x11, f12 x12, f13 x13)

-- |
-- >>> nmap <#> (+1) <#> (+2) <#> (+3) <#> (+4) <#> (+5) <#> (+6) <#> (+7) <#> (+8) <#> (+9) <#> (+10) <#> (+11) <#> (+12) <#> (+13) <#> (+14) $ (0::Int, 0::Int, 0::Int, 0::Int, 0::Int, 0::Int, 0::Int, 0::Int, 0::Int, 0::Int, 0::Int, 0::Int, 0::Int, 0::Int)
-- (1,2,3,4,5,6,7,8,9,10,11,12,13,14)
instance NFunctor (,,,,,,,,,,,,,) where
  nmap = NMap1 $ \f1
      -> NMap1 $ \f2
      -> NMap1 $ \f3
      -> NMap1 $ \f4
      -> NMap1 $ \f5
      -> NMap1 $ \f6
      -> NMap1 $ \f7
      -> NMap1 $ \f8
      -> NMap1 $ \f9
      -> NMap1 $ \f10
      -> NMap1 $ \f11
      -> NMap1 $ \f12
      -> NMap1 $ \f13
      -> NMap1 $ \f14
      -> \(x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14)
      -> (f1 x1, f2 x2, f3 x3, f4 x4, f5 x5, f6 x6, f7 x7, f8 x8, f9 x9, f10 x10, f11 x11, f12 x12, f13 x13, f14 x14)

-- |
-- >>> nmap <#> (+1) <#> (+2) <#> (+3) <#> (+4) <#> (+5) <#> (+6) <#> (+7) <#> (+8) <#> (+9) <#> (+10) <#> (+11) <#> (+12) <#> (+13) <#> (+14) <#> (+15) $ (0::Int, 0::Int, 0::Int, 0::Int, 0::Int, 0::Int, 0::Int, 0::Int, 0::Int, 0::Int, 0::Int, 0::Int, 0::Int, 0::Int, 0::Int)
-- (1,2,3,4,5,6,7,8,9,10,11,12,13,14,15)
instance NFunctor (,,,,,,,,,,,,,,) where
  nmap = NMap1 $ \f1
      -> NMap1 $ \f2
      -> NMap1 $ \f3
      -> NMap1 $ \f4
      -> NMap1 $ \f5
      -> NMap1 $ \f6
      -> NMap1 $ \f7
      -> NMap1 $ \f8
      -> NMap1 $ \f9
      -> NMap1 $ \f10
      -> NMap1 $ \f11
      -> NMap1 $ \f12
      -> NMap1 $ \f13
      -> NMap1 $ \f14
      -> NMap1 $ \f15
      -> \(x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15)
      -> (f1 x1, f2 x2, f3 x3, f4 x4, f5 x5, f6 x6, f7 x7, f8 x8, f9 x9, f10 x10, f11 x11, f12 x12, f13 x13, f14 x14, f15 x15)

-- 16-tuples don't even have a Show instance, so we don't bother with an NFunctor instance either
