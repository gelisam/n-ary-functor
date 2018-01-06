{-# LANGUAGE RankNTypes, TypeFamilies, TypeFamilyDependencies, TypeInType #-}
module NAryFunctor
  ( NFunctor(..)

  -- * Internals
  , NMap1(..), NMap
  ) where

import Data.Bifunctor
import Data.Functor.Identity
import Data.Kind (Type)


-- |
-- A generalization of 'Functor', 'Bifunctor', 'Trifunctor', etc.
--
-- Example usage:
--
-- >>> nmap <#> (+1) $ Identity (0::Int)
-- Identity 1
--
-- >>> nmap <#> (+1) <#> (+2) $ (0::Int, 0::Int)
-- (1,2)
--
-- >>> nmap <#> (+1) <#> (+2) <#> (+3) $ (0::Int, 0::Int, 0::Int)
-- (1,2,3)
--
-- Laws:
--
-- > nmap <#> id <#> ... <#> id = id
-- > (nmap <#> f1 <#> ... <#> fN) . (nmap <#> g1 <#> ... <#> gN) = nmap <#> (f1 . g1) <#> ... <#> (fN . gN)
--
-- Example instance:
--
-- > instance NFunctor (,,) where
-- >   nmap = NMap1 $ \f1
-- >       -> NMap1 $ \f2
-- >       -> NMap1 $ \f3
-- >       -> \(x1,x2,x3)
-- >       -> (f1 x1, f2 x2, f3 x3)
class NFunctor (f :: k) where
  nmap :: NMap k f f


-- |
-- Types like 'Either' which have both a 'Functor' and a 'Bifunctor' instance
-- can have more than one 'NFunctor' instance. Those instances all define the
-- same method, 'nmap', but they return a value of a different type, which is
-- how the correct 'NFunctor' instance is picked:
--
-- > nmap :: NMap1 Type (Either a) (Either a)    -- Functor
-- > nmap :: NMap1 (Type -> Type) Either Either  -- Bifunctor
--
-- This 'NMap1' is unwrapped by using '<#>' to pass in the next input function.
-- In the case of @NMap1 (Type -> Type)@, the result after passing this input
-- function is another 'NMap1', which needs to be unwrapped using a second
-- '<#>'. The end result is that the 'Functor' behaviour is obtained by using a
-- single '<#>', and the 'Bifunctor' behaviour is obtained by using two.
--
-- >>> nmap <#> (+1) $ Right (0::Int)
-- Right 1
-- >>> nmap <#> (+1) <#> (+2) $ Left (0::Int)
-- Left 1
newtype NMap1 k (f :: Type -> k) (f' :: Type -> k) = NMap1
  { (<#>) :: forall a b. (a -> b) -> NMap k (f a) (f' b)
  }

type family NMap k = (r :: k -> k -> Type) | r -> k where
  NMap Type        = (->)
  NMap (Type -> k) = NMap1 k


-- | For kind @* -> *@ ('Functor'), 'nmap' must be @NMap1 fmap@.
--
-- >>> nmap <#> (+1) $ Right (0::Int)
-- Right 1
instance NFunctor (Either a) where
  nmap = NMap1 fmap

-- | For kind @* -> * -> *@ ('Bifunctor'), 'nmap' must be @NMap1 $ \f1 -> NMap1 $ \f2 -> bimap f1 f2@.
--
-- >>> nmap <#> (+1) <#> (+2) $ Left (0::Int)
-- Left 1
instance NFunctor Either where
  nmap = NMap1 $ \f1 -> NMap1 $ \f2 -> bimap f1 f2


-- |
-- For kind @*@, 'nmap' must be the identity function. If 'Bifunctor' and
-- 'Functor' correspond to binary and unary functors, this corresponds to a
-- "nullary" functor.
--
-- >>> nmap ()
-- ()
instance NFunctor () where
  nmap = id

instance NFunctor Identity where
  nmap = NMap1 $ \f1
      -> \(Identity x1)
      -> Identity (f1 x1)

instance NFunctor (,) where
  nmap = NMap1 $ \f1
      -> NMap1 $ \f2
      -> \(x1,x2)
      -> (f1 x1, f2 x2)

instance NFunctor (,,) where
  nmap = NMap1 $ \f1
      -> NMap1 $ \f2
      -> NMap1 $ \f3
      -> \(x1,x2,x3)
      -> (f1 x1, f2 x2, f3 x3)

instance NFunctor (,,,) where
  nmap = NMap1 $ \f1
      -> NMap1 $ \f2
      -> NMap1 $ \f3
      -> NMap1 $ \f4
      -> \(x1,x2,x3,x4)
      -> (f1 x1, f2 x2, f3 x3, f4 x4)

instance NFunctor (,,,,) where
  nmap = NMap1 $ \f1
      -> NMap1 $ \f2
      -> NMap1 $ \f3
      -> NMap1 $ \f4
      -> NMap1 $ \f5
      -> \(x1,x2,x3,x4,x5)
      -> (f1 x1, f2 x2, f3 x3, f4 x4, f5 x5)

instance NFunctor (,,,,,) where
  nmap = NMap1 $ \f1
      -> NMap1 $ \f2
      -> NMap1 $ \f3
      -> NMap1 $ \f4
      -> NMap1 $ \f5
      -> NMap1 $ \f6
      -> \(x1,x2,x3,x4,x5,x6)
      -> (f1 x1, f2 x2, f3 x3, f4 x4, f5 x5, f6 x6)

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
