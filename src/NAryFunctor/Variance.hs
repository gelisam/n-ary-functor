{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, PolyKinds, RankNTypes, TypeFamilies, UndecidableInstances, UnicodeSyntax #-}
module NAryFunctor.Variance where

import Control.Monad.Trans.State
import Data.Bifunctor
import Data.Functor.Const


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


-- Instances

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
