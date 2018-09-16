{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, PolyKinds, RankNTypes, TypeFamilies, UndecidableInstances, UnicodeSyntax #-}
module NAryFunctor.Variance where

import Control.Arrow
import Control.Monad.Trans.State
import Data.Bifunctor
import Data.Functor.Const

-- $setup
-- >>> import Control.Monad
-- >>> import Control.Monad.IO.Class
-- >>> import Data.Functor.Identity


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
