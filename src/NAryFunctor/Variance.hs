{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, PolyKinds, RankNTypes, TypeFamilies, UndecidableInstances, UnicodeSyntax #-}
module NAryFunctor.Variance where

import Control.Monad.Trans.State
import Data.Bifunctor
import Data.Functor.Const


class VFunctor (v :: k -> k -> *) (f :: k) where
  vmap :: v f f


-- Internals

data Nonvariant1 a cc f f' = Nonvariant1
  { (-#-) :: () -> cc (f a) (f' a) }

data Invariant1 cc f f' = Invariant1
  { (<#>/>#<) :: forall a a'. (a -> a', a' -> a) -> cc (f a) (f' a') }

data Covariant1 cc f f' = Covariant1
  { (<#>) :: forall a a'. (a -> a') -> cc (f a) (f' a') }

data Contravariant1 cc f f' = Contravariant1
  { (>#<) :: forall a a'. (a' -> a) -> cc (f a) (f' a') }

data Phantomvariant1 cc f f' = Phantomvariant1
  { (👻#👻) :: forall a a'. () -> cc (f a) (f' a') }


-- Instances

-- |
-- >>> :{
-- let length' :: Int -> String
--     length' = vmap >#< show <#> show $ length
-- in length' 100
-- :}
-- "3"
instance v ~ Contravariant1 (Covariant1 (->)) => VFunctor v (->) where
  vmap = Contravariant1 $ \f1'
      -> Covariant1 $ \f2
      -> \g
      -> f2 . g . f1'

-- |
-- >>> vmap <#> length 👻#👻 () $ Const "foo"
-- Const 3
instance v ~ Covariant1 (Phantomvariant1 (->)) => VFunctor v Const where
  vmap = Covariant1 $ \f1
      -> Phantomvariant1 $ \()
      -> \(Const x1)
      -> Const (f1 x1)

-- |
-- >>> :{
-- let action :: State Int ()
--     action = modify (+1)
--     action' :: State String ()
--     action' = vmap <#>/>#< (show,read) -#- () <#> id $ action
-- in execState action' "42"
-- :}
-- "43"
instance ( v ~ Invariant1 (Nonvariant1 m (Covariant1 (->)))
         , Functor m
         ) => VFunctor v StateT where
  vmap = Invariant1 $ \(f1,f1')
      -> Nonvariant1 $ \()
      -> Covariant1 $ \f3
      -> \(StateT body)
      -> StateT (fmap (bimap f3 f1) . body . f1')
