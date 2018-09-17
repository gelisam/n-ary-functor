{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, PolyKinds, RankNTypes, TypeFamilies, UndecidableInstances, UnicodeSyntax #-}
module NAryFunctor.Variance where

import Control.Arrow
import Control.Monad.Trans.State
import Data.Bifunctor
import Data.Functor.Const
import Data.Functor.Identity

-- $setup
-- >>> import Control.Monad
-- >>> import Control.Monad.IO.Class


class VFunctor (f :: k) where
  type VMap f :: k -> k -> *
  vmap :: VMap f f f


newtype CovariantMap1 cc f f' = CovariantMap1
  { (<#>) :: forall a a'
           . (a -> a')
          -> cc (f a) (f' a')
  }

newtype ContravariantMap1 cc f f' = ContravariantMap1
  { (>#<) :: forall a a'
           . (a' -> a)
          -> cc (f a) (f' a')
  }

newtype InvariantMap1 cc f f' = InvariantMap1
  { (<#>/>#<) :: forall a a'
               . (a -> a', a' -> a)
              -> cc (f a) (f' a')
  }

newtype PhantomvariantMap1 cc f f' = PhantomvariantMap1
  { (👻#👻) :: forall a a'
             . ()
            -> cc (f a) (f' a')
  }



newtype NF m m' = NF
  { runNF :: forall a. m a -> m' a
  }

newtype Covariant1Map1 cc f f' = Covariant1Map1
  { (<##>) :: forall m m'. (Functor m, Functor m')
           => NF m m'
           -> cc (f m) (f' m')
  }

newtype Contravariant1Map1 cc f f' = Contravariant1Map1
  { (>##<) :: forall m m'. (Functor m, Functor m')
           => NF m' m
           -> cc (f m) (f' m')
  }

newtype Invariant1Map1 cc f f' = Invariant1Map1
  { (<##>/>##<) :: forall m m'. (Functor m, Functor m')
                => (NF m m', NF m' m)
                -> cc (f m) (f' m')
  }


-- Instances

-- |
-- >>> vmap <#> (+1) $ Right (0::Int)
-- Right 1
instance VFunctor (Either a) where
  type VMap (Either a) = CovariantMap1 (->)
  vmap = CovariantMap1 $ \f1
      -> fmap f1

-- |
-- >>> vmap <#> (+1) <#> (+2) $ Left (0::Int)
-- Left 1
instance VFunctor Either where
  type VMap Either = CovariantMap1 (CovariantMap1 (->))
  vmap = CovariantMap1 $ \f1
      -> CovariantMap1 $ \f2
      -> bimap f1 f2

-- |
-- >>> :{
-- let length' :: Int -> String
--     length' = vmap >#< show <#> show $ length
-- in length' 100
-- :}
-- "3"
instance VFunctor (->) where
  type VMap (->) = ContravariantMap1 (CovariantMap1 (->))
  vmap = ContravariantMap1 $ \f1'
      -> CovariantMap1 $ \f2
      -> \g
      -> f2 . g . f1'

-- |
-- >>> :{
-- let divideState :: Double -> StateT Double Identity ()
--     divideState x = do
--       modify (/ x)
--     divideState' :: Int -> StateT Int Maybe ()
--     divideState' x = do
--       guard (x /= 0)
--       vmap <#>/>#< (round, fromIntegral)
--               <##> NF (Just . runIdentity)
--                <#> id
--                  $ divideState (fromIntegral x)
-- in execStateT (divideState' 2) 6
-- :}
-- Just 3
instance VFunctor StateT where
  type VMap StateT = InvariantMap1 (Covariant1Map1 (CovariantMap1 (->)))
  vmap = InvariantMap1 $ \(f1, f1')
      -> Covariant1Map1 $ \f2
      -> CovariantMap1 $ \f3
      -> \body
      -> StateT $ \s'
      -> fmap (f3 *** f1) $ runNF f2 $ runStateT body $ f1' s'


-- |
-- For kind @*@, 'vmap' must be the identity function. If 'Bifunctor' and
-- 'Functor' correspond to binary and unary functors, this corresponds to a
-- "nullary" functor.
--
-- >>> vmap ()
-- ()
instance VFunctor () where
  type VMap () = (->)
  vmap = id

-- |
-- >>> vmap <#> length $ Identity "abc"
-- Identity 3
instance VFunctor Identity where
  type VMap Identity = CovariantMap1 (->)
  vmap = CovariantMap1 $ \f1
      -> \(Identity x1)
      -> Identity (f1 x1)

-- |
-- >>> vmap <#> length <#> length $ ("abc", "abcde")
-- (3,5)
instance VFunctor (,) where
  type VMap (,) = CovariantMap1 (CovariantMap1 (->))
  vmap = CovariantMap1 $ \f1
      -> CovariantMap1 $ \f2
      -> \(x1,x2)
      -> (f1 x1, f2 x2)

-- |
-- >>> vmap <#> length <#> length <#> length $ ("abc", "abcde", "abcdefg")
-- (3,5,7)
instance VFunctor (,,) where
  type VMap (,,) = CovariantMap1 (CovariantMap1 (CovariantMap1 (->)))
  vmap = CovariantMap1 $ \f1
      -> CovariantMap1 $ \f2
      -> CovariantMap1 $ \f3
      -> \(x1,x2,x3)
      -> (f1 x1, f2 x2, f3 x3)

instance VFunctor (,,,) where
  type VMap (,,,) = CovariantMap1 (CovariantMap1 (CovariantMap1 (CovariantMap1 (->))))
  vmap = CovariantMap1 $ \f1
      -> CovariantMap1 $ \f2
      -> CovariantMap1 $ \f3
      -> CovariantMap1 $ \f4
      -> \(x1,x2,x3,x4)
      -> (f1 x1, f2 x2, f3 x3, f4 x4)

instance VFunctor (,,,,) where
  type VMap (,,,,) = CovariantMap1 (CovariantMap1 (CovariantMap1 (CovariantMap1 (CovariantMap1 (->)))))
  vmap = CovariantMap1 $ \f1
      -> CovariantMap1 $ \f2
      -> CovariantMap1 $ \f3
      -> CovariantMap1 $ \f4
      -> CovariantMap1 $ \f5
      -> \(x1,x2,x3,x4,x5)
      -> (f1 x1, f2 x2, f3 x3, f4 x4, f5 x5)

instance VFunctor (,,,,,) where
  type VMap (,,,,,) = CovariantMap1 (CovariantMap1 (CovariantMap1 (CovariantMap1 (CovariantMap1 (CovariantMap1 (->))))))
  vmap = CovariantMap1 $ \f1
      -> CovariantMap1 $ \f2
      -> CovariantMap1 $ \f3
      -> CovariantMap1 $ \f4
      -> CovariantMap1 $ \f5
      -> CovariantMap1 $ \f6
      -> \(x1,x2,x3,x4,x5,x6)
      -> (f1 x1, f2 x2, f3 x3, f4 x4, f5 x5, f6 x6)

instance VFunctor (,,,,,,) where
  type VMap (,,,,,,) = CovariantMap1 (CovariantMap1 (CovariantMap1 (CovariantMap1 (CovariantMap1 (CovariantMap1 (CovariantMap1 (->)))))))
  vmap = CovariantMap1 $ \f1
      -> CovariantMap1 $ \f2
      -> CovariantMap1 $ \f3
      -> CovariantMap1 $ \f4
      -> CovariantMap1 $ \f5
      -> CovariantMap1 $ \f6
      -> CovariantMap1 $ \f7
      -> \(x1,x2,x3,x4,x5,x6,x7)
      -> (f1 x1, f2 x2, f3 x3, f4 x4, f5 x5, f6 x6, f7 x7)

instance VFunctor (,,,,,,,) where
  type VMap (,,,,,,,) = CovariantMap1 (CovariantMap1 (CovariantMap1 (CovariantMap1 (CovariantMap1 (CovariantMap1 (CovariantMap1 (CovariantMap1 (->))))))))
  vmap = CovariantMap1 $ \f1
      -> CovariantMap1 $ \f2
      -> CovariantMap1 $ \f3
      -> CovariantMap1 $ \f4
      -> CovariantMap1 $ \f5
      -> CovariantMap1 $ \f6
      -> CovariantMap1 $ \f7
      -> CovariantMap1 $ \f8
      -> \(x1,x2,x3,x4,x5,x6,x7,x8)
      -> (f1 x1, f2 x2, f3 x3, f4 x4, f5 x5, f6 x6, f7 x7, f8 x8)

instance VFunctor (,,,,,,,,) where
  type VMap (,,,,,,,,) = CovariantMap1 (CovariantMap1 (CovariantMap1 (CovariantMap1 (CovariantMap1 (CovariantMap1 (CovariantMap1 (CovariantMap1 (CovariantMap1 (->)))))))))
  vmap = CovariantMap1 $ \f1
      -> CovariantMap1 $ \f2
      -> CovariantMap1 $ \f3
      -> CovariantMap1 $ \f4
      -> CovariantMap1 $ \f5
      -> CovariantMap1 $ \f6
      -> CovariantMap1 $ \f7
      -> CovariantMap1 $ \f8
      -> CovariantMap1 $ \f9
      -> \(x1,x2,x3,x4,x5,x6,x7,x8,x9)
      -> (f1 x1, f2 x2, f3 x3, f4 x4, f5 x5, f6 x6, f7 x7, f8 x8, f9 x9)

instance VFunctor (,,,,,,,,,) where
  type VMap (,,,,,,,,,) = CovariantMap1 (CovariantMap1 (CovariantMap1 (CovariantMap1 (CovariantMap1 (CovariantMap1 (CovariantMap1 (CovariantMap1 (CovariantMap1 (CovariantMap1 (->))))))))))
  vmap = CovariantMap1 $ \f1
      -> CovariantMap1 $ \f2
      -> CovariantMap1 $ \f3
      -> CovariantMap1 $ \f4
      -> CovariantMap1 $ \f5
      -> CovariantMap1 $ \f6
      -> CovariantMap1 $ \f7
      -> CovariantMap1 $ \f8
      -> CovariantMap1 $ \f9
      -> CovariantMap1 $ \f10
      -> \(x1,x2,x3,x4,x5,x6,x7,x8,x9,x10)
      -> (f1 x1, f2 x2, f3 x3, f4 x4, f5 x5, f6 x6, f7 x7, f8 x8, f9 x9, f10 x10)

instance VFunctor (,,,,,,,,,,) where
  type VMap (,,,,,,,,,,) = CovariantMap1 (CovariantMap1 (CovariantMap1 (CovariantMap1 (CovariantMap1 (CovariantMap1 (CovariantMap1 (CovariantMap1 (CovariantMap1 (CovariantMap1 (CovariantMap1 (->)))))))))))
  vmap = CovariantMap1 $ \f1
      -> CovariantMap1 $ \f2
      -> CovariantMap1 $ \f3
      -> CovariantMap1 $ \f4
      -> CovariantMap1 $ \f5
      -> CovariantMap1 $ \f6
      -> CovariantMap1 $ \f7
      -> CovariantMap1 $ \f8
      -> CovariantMap1 $ \f9
      -> CovariantMap1 $ \f10
      -> CovariantMap1 $ \f11
      -> \(x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11)
      -> (f1 x1, f2 x2, f3 x3, f4 x4, f5 x5, f6 x6, f7 x7, f8 x8, f9 x9, f10 x10, f11 x11)

instance VFunctor (,,,,,,,,,,,) where
  type VMap (,,,,,,,,,,,) = CovariantMap1 (CovariantMap1 (CovariantMap1 (CovariantMap1 (CovariantMap1 (CovariantMap1 (CovariantMap1 (CovariantMap1 (CovariantMap1 (CovariantMap1 (CovariantMap1 (CovariantMap1 (->))))))))))))
  vmap = CovariantMap1 $ \f1
      -> CovariantMap1 $ \f2
      -> CovariantMap1 $ \f3
      -> CovariantMap1 $ \f4
      -> CovariantMap1 $ \f5
      -> CovariantMap1 $ \f6
      -> CovariantMap1 $ \f7
      -> CovariantMap1 $ \f8
      -> CovariantMap1 $ \f9
      -> CovariantMap1 $ \f10
      -> CovariantMap1 $ \f11
      -> CovariantMap1 $ \f12
      -> \(x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12)
      -> (f1 x1, f2 x2, f3 x3, f4 x4, f5 x5, f6 x6, f7 x7, f8 x8, f9 x9, f10 x10, f11 x11, f12 x12)

instance VFunctor (,,,,,,,,,,,,) where
  type VMap (,,,,,,,,,,,,) = CovariantMap1 (CovariantMap1 (CovariantMap1 (CovariantMap1 (CovariantMap1 (CovariantMap1 (CovariantMap1 (CovariantMap1 (CovariantMap1 (CovariantMap1 (CovariantMap1 (CovariantMap1 (CovariantMap1 (->)))))))))))))
  vmap = CovariantMap1 $ \f1
      -> CovariantMap1 $ \f2
      -> CovariantMap1 $ \f3
      -> CovariantMap1 $ \f4
      -> CovariantMap1 $ \f5
      -> CovariantMap1 $ \f6
      -> CovariantMap1 $ \f7
      -> CovariantMap1 $ \f8
      -> CovariantMap1 $ \f9
      -> CovariantMap1 $ \f10
      -> CovariantMap1 $ \f11
      -> CovariantMap1 $ \f12
      -> CovariantMap1 $ \f13
      -> \(x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13)
      -> (f1 x1, f2 x2, f3 x3, f4 x4, f5 x5, f6 x6, f7 x7, f8 x8, f9 x9, f10 x10, f11 x11, f12 x12, f13 x13)

instance VFunctor (,,,,,,,,,,,,,) where
  type VMap (,,,,,,,,,,,,,) = CovariantMap1 (CovariantMap1 (CovariantMap1 (CovariantMap1 (CovariantMap1 (CovariantMap1 (CovariantMap1 (CovariantMap1 (CovariantMap1 (CovariantMap1 (CovariantMap1 (CovariantMap1 (CovariantMap1 (CovariantMap1 (->))))))))))))))
  vmap = CovariantMap1 $ \f1
      -> CovariantMap1 $ \f2
      -> CovariantMap1 $ \f3
      -> CovariantMap1 $ \f4
      -> CovariantMap1 $ \f5
      -> CovariantMap1 $ \f6
      -> CovariantMap1 $ \f7
      -> CovariantMap1 $ \f8
      -> CovariantMap1 $ \f9
      -> CovariantMap1 $ \f10
      -> CovariantMap1 $ \f11
      -> CovariantMap1 $ \f12
      -> CovariantMap1 $ \f13
      -> CovariantMap1 $ \f14
      -> \(x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14)
      -> (f1 x1, f2 x2, f3 x3, f4 x4, f5 x5, f6 x6, f7 x7, f8 x8, f9 x9, f10 x10, f11 x11, f12 x12, f13 x13, f14 x14)

instance VFunctor (,,,,,,,,,,,,,,) where
  type VMap (,,,,,,,,,,,,,,) = CovariantMap1 (CovariantMap1 (CovariantMap1 (CovariantMap1 (CovariantMap1 (CovariantMap1 (CovariantMap1 (CovariantMap1 (CovariantMap1 (CovariantMap1 (CovariantMap1 (CovariantMap1 (CovariantMap1 (CovariantMap1 (CovariantMap1 (->)))))))))))))))
  vmap = CovariantMap1 $ \f1
      -> CovariantMap1 $ \f2
      -> CovariantMap1 $ \f3
      -> CovariantMap1 $ \f4
      -> CovariantMap1 $ \f5
      -> CovariantMap1 $ \f6
      -> CovariantMap1 $ \f7
      -> CovariantMap1 $ \f8
      -> CovariantMap1 $ \f9
      -> CovariantMap1 $ \f10
      -> CovariantMap1 $ \f11
      -> CovariantMap1 $ \f12
      -> CovariantMap1 $ \f13
      -> CovariantMap1 $ \f14
      -> CovariantMap1 $ \f15
      -> \(x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15)
      -> (f1 x1, f2 x2, f3 x3, f4 x4, f5 x5, f6 x6, f7 x7, f8 x8, f9 x9, f10 x10, f11 x11, f12 x12, f13 x13, f14 x14, f15 x15)

-- 16-tuples don't even have a Show instance, so we don't bother with an VFunctor instance either
