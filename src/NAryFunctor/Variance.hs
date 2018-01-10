{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, PolyKinds, RankNTypes, TypeFamilies, UndecidableInstances, UnicodeSyntax #-}
module NAryFunctor.Variance where

import Control.Monad.Trans.State
import Data.Bifunctor
import Data.Functor.Const


class VFunctor (v :: k -> k -> *) (f :: k) where
  vmap :: v f f


-- Internals

class Nonvariant v a where
  (-#-) :: forall cc f f'. v cc f f' -> () -> cc (f a) (f' a)

class Invariant v where
  (<#>/>#<) :: forall cc f f' a a'. v cc f f' -> (a -> a', a' -> a) -> cc (f a) (f' a')

class Invariant v => Covariant v where
  (<#>) :: forall cc f f' a a'. v cc f f' -> (a -> a') -> cc (f a) (f' a')

class Invariant v => Contravariant v where
  (>#<) :: forall cc f f' a a'. v cc f  f' -> (a' -> a) -> cc (f a) (f' a')

class Phantomvariant v where
  (👻#👻) :: forall cc f f' a a'. v cc f f' -> () -> cc (f a) (f' a')


data Nonvariant1 a cc f f' = Nonvariant1
  { unNonvariant1 :: () -> cc (f a) (f' a) }

data Invariant1 cc f f' = Invariant1
  { unInvariant1 :: forall a a'. (a -> a', a' -> a) -> cc (f a) (f' a') }

data Covariant1 cc f f' = Covariant1
  { unCovariant1 :: forall a a'. (a -> a') -> cc (f a) (f' a') }

data Contravariant1 cc f f' = Contravariant1
  { unContravariant1 :: forall a a'. (a' -> a) -> cc (f a) (f' a') }

data Phantomvariant1 cc f f' = Phantomvariant1
  { unPhantomvariant1 :: forall a a'. () -> cc (f a) (f' a') }


instance a ~ a' => Nonvariant (Nonvariant1 a) a' where
  Nonvariant1 body -#- () = body ()


instance Nonvariant Invariant1 a where
  Invariant1 body -#- () = body (id,id)

instance Invariant Invariant1 where
  Invariant1 body <#>/>#< (f,f') = body (f,f')


instance Nonvariant Covariant1 a where
  Covariant1 body -#- () = body id

instance Invariant Covariant1 where
  Covariant1 body <#>/>#< (f,_) = body f

instance Covariant Covariant1 where
  Covariant1 body <#> f = body f


instance Nonvariant Contravariant1 a where
  Contravariant1 body -#- () = body id

instance Invariant Contravariant1 where
  Contravariant1 body <#>/>#< (_,f') = body f'

instance Contravariant Contravariant1 where
  Contravariant1 body >#< f' = body f'


instance Nonvariant Phantomvariant1 a where
  Phantomvariant1 body -#- () = body ()

instance Invariant Phantomvariant1 where
  Phantomvariant1 body <#>/>#< _ = body ()

instance Covariant Phantomvariant1 where
  Phantomvariant1 body <#> _ = body ()

instance Contravariant Phantomvariant1 where
  Phantomvariant1 body >#< _ = body ()

instance Phantomvariant Phantomvariant1 where
  Phantomvariant1 body 👻#👻 () = body ()


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
--     action' = vmap <#>/>#< (show,read) -#- () -#- () $ action
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
