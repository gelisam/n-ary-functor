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
