{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, PolyKinds, RankNTypes, TypeFamilies, TypeOperators, UndecidableInstances, UnicodeSyntax #-}
module NAryFunctor.Variance where

import Control.Arrow
import Control.Monad.Trans.Reader
import Control.Monad.Trans.State
import Data.Bifunctor
import Data.Functor.Const
import Data.Functor.Identity

import NAryFunctor.NF

-- $setup
-- >>> import Control.Monad
-- >>> import Control.Monad.IO.Class


-- |
-- A generalization of 'Functor', 'Bifunctor', 'Trifunctor', etc., but also a
-- generalization of 'Contravariant', 'Invariant', 'Profunctor', and 'MFunctor'.
-- We can 'vmap' over all three type parameters of 'StateT' even though they
-- have different kinds and different variances.
--
-- Let's look at the generalization of 'Functor' to n-ary functors first.
--
-- Example usage:
--
-- >>> vmap <#> (+1) $ Identity (0::Int)
-- Identity 1
--
-- >>> vmap <#> (+1) <#> (+2) $ (0::Int, 0::Int)
-- (1,2)
--
-- >>> vmap <#> (+1) <#> (+2) <#> (+3) $ (0::Int, 0::Int, 0::Int)
-- (1,2,3)
--
-- Laws:
--
-- > vmap <#> id <#> ... <#> id = id
-- > (vmap <#> f1 <#> ... <#> fN) . (vmap <#> g1 <#> ... <#> gN) = vmap <#> (f1 . g1) <#> ... <#> (fN . gN)
--
-- Example instance:
--
-- > instance VFunctor (,,) where
-- >   type VMap (,,) = CovariantT (CovariantT (CovariantT (->)))
-- >   vmap = ...
--
-- The associated type 'VMap' is the type of 'vmap'. It is constructed by
-- composing "mapping type transformers" and applying them to the identity
-- mapping type, the function type @(->)@. A mapping type is a type such as
-- @fmap@'s or @bimap@'s, which takes as input one function over each type
-- parameter and converts them into a function over the datatype.
--
-- When generalizing 'Functor' to an n-ary functor, all those input functions
-- are covariant, and so we need to compose @n@ copies of the 'CovariantT'
-- mapping type transformer. Let's consider the case @n = 2@. With two copies
-- of 'CovariantT', the type of 'vmap' is @CovariantT (CovariantT (->)) f f@,
-- so when calling 'vmap', we need to unwrap two layers of 'CovariantT'. The
-- unwrapping function is named @(\<\#\>)@, not @runCovariantT@, so the call
-- @vmap \<\#\> g \<\#\> h@ is unwrapping the two 'CovariantT' layers in order
-- to produce a value in the identity mapping type @(->)@, namely a function of
-- type @f a b -> f a' b'@. In those two calls, the type of @(\<\#\>)@ gets
-- specialized as follows:
--
-- > (<#>) :: CovariantT (CovariantT (->)) f f
-- >       -> (a -> a')
-- >       -> CovariantT (->) (f a) (f a')
-- >
-- > (<#>) :: CovariantT (->) (f a) (f a')
-- >       -> (b -> b')
-- >       -> f a b -> f a' b'
--
-- Next, let's see how this approach allows us to 'vmap' over all three type
-- parameters of 'StateT'. This time, the instance looks like this:
--
-- > instance VFunctor StateT where
-- >   type VMap StateT = InvariantT (Covariant1T (CovariantT (->)))
-- >   vmap = ...
--
-- 'StateT' has three type parameters, 's', 'm', and 'a'. We will thus need to
-- compose three mapping type transformers. Since a 'StateT' computation both
-- receives an 's' and produces an 's', this type parameter is "invariant"; a
-- standard but confusing name which does /not/ mean that the parameter cannot
-- vary, but rather that we need both a function from 's' to 's'' and a
-- function from 's'' back to 's' in order to convert a @StateT s m a@ into a
-- @StateT s' m a@. By contrast, the 'a' type parameter is covariant, because
-- we only need a function from 'a' to 'a'' in order to convert a @StateT s m
-- a@ into a @StateT s m a'@.
--
-- As for the 'm' type parameter, we need a natural transformation @forall x. m
-- x -> m' x@ in order to convert a @StateT s m a@ into a @StateT s m' a@. This
-- is still covariant, but for a type parameter of kind @* -> *@, so we follow the
-- [convention](http://hackage.haskell.org/package/base-4.11.1.0/docs/Data-Functor-Classes.html)
-- and add a @1@ to the name of the mapping type transformer. To 'vmap' over
-- all three type parameters, the three mapping type transformers we must
-- combine are thus 'InvariantT', 'Covariant1T', and 'CovariantT', and so the
-- type of @StateT@'s 'vmap' is @InvariantT (Covariant1T (CovariantT (->)))@.
-- Each of these is unwrapped via a different infix operator:
-- @vmap \<\#\>/\>\#\< (f,f') \<\#\#\> NF g \<\#\> h@, whose types get
-- specialized as follows:
--
-- > (<#>/>#<) :: InvariantT (Covariant1T (CovariantT (->))) StateT StateT
-- >           -> (s -> s', s' -> s)
-- >           -> Covariant1T (CovariantT (->)) (StateT s) (StateT s')
-- >
-- > (<##>) :: (Functor m, Functor m')
-- >        => Covariant1T (CovariantT (->)) (StateT s) (StateT s')
-- >        -> NF m m'
-- >        -> CovariantT (->) (StateT s m) (StateT s' m')
-- >
-- > (<#>) :: CovariantT (->) (StateT s m) (StateT s' m')
-- >       -> (a -> a')
-- >       -> StateT s m a -> StateT s' m' a'
--
-- Since 'vmap' can have so many different types, it's a bit hard to state the
-- laws in general, but it's the obvious ones: using 'id' everywhere yields
-- 'id', and two composed 'vmap's is equivalent to a single 'vmap' in which the
-- functions are composed; covariantly or contravariantly, as appropriate. For
-- example, the laws for @StateT@'s 'vmap' are:
--
-- > vmap <#>/>#< (id,id) <##> id <#> id = id
-- > (vmap <#>/>#< (f1,f1') <##> f2 <#> f3) . (vmap <#>/>#< (g1,g1') <##> g2 <#> g3) = vmap <#>/>#< (f1 . g1, g1' . f1') <##> (f2 . g2) <#> (f3 . g3)
class VFunctor (f :: k) where
  type VMap f :: k -> k -> *
  vmap :: VMap f f f


newtype CovariantT to f f' = CovariantT
  { (<#>) :: forall a a'
           . (a -> a')
          -> f a `to` f' a'
  }

newtype ContravariantT to f f' = ContravariantT
  { (>#<) :: forall a a'
           . (a' -> a)
          -> f a `to` f' a'
  }

newtype InvariantT to f f' = InvariantT
  { (<#>/>#<) :: forall a a'
               . (a -> a', a' -> a)
              -> f a `to` f' a'
  }

newtype PhantomvariantT to f f' = PhantomvariantT
  { (👻#👻) :: forall a a'
             . ()
            -> f a `to` f' a'
  }



newtype Covariant1T to f f' = Covariant1T
  { (<##>) :: forall m m'. (Functor m, Functor m')
           => NF m m'
           -> f m `to` f' m'
  }

newtype Contravariant1T to f f' = Contravariant1T
  { (>##<) :: forall m m'. (Functor m, Functor m')
           => NF m' m
           -> f m `to` f' m'
  }

newtype Invariant1T to f f' = Invariant1T
  { (<##>/>##<) :: forall m m'. (Functor m, Functor m')
                => (NF m m', NF m' m)
                -> f m `to` f' m'
  }


-- Instances

-- |
-- >>> vmap <#> (+1) $ Right (0::Int)
-- Right 1
instance VFunctor (Either a) where
  type VMap (Either a) = CovariantT (->)
  vmap = CovariantT $ \f1
      -> fmap f1

-- |
-- >>> vmap <#> (+1) <#> (+2) $ Left (0::Int)
-- Left 1
instance VFunctor Either where
  type VMap Either = CovariantT (CovariantT (->))
  vmap = CovariantT $ \f1
      -> CovariantT $ \f2
      -> bimap f1 f2

-- |
-- >>> :{
-- let length' :: Int -> String
--     length' = vmap >#< show <#> show $ length
-- in length' 100
-- :}
-- "3"
instance VFunctor (->) where
  type VMap (->) = ContravariantT (CovariantT (->))
  vmap = ContravariantT $ \f1'
      -> CovariantT $ \f2
      -> \g
      -> f2 . g . f1'

instance VFunctor NF where
  type VMap NF = Contravariant1T (Covariant1T (->))
  vmap = Contravariant1T $ \(NF f1')
      -> Covariant1T $ \(NF f2)
      -> \(NF g)
      -> NF (f2 . g . f1')

-- |
-- >>> :{
-- let divideReader :: Double -> ReaderT Double Identity Double
--     divideReader x = (/ x) <$> ask
--     divideReader' :: Int -> ReaderT Int Maybe Int
--     divideReader' x = do
--       guard (x /= 0)
--       vmap >#< fromIntegral
--           <##> NF (Just . runIdentity)
--            <#> round
--              $ divideReader (fromIntegral x)
-- in runReaderT (divideReader' 2) 6
-- :}
-- Just 3
instance VFunctor (ReaderT :: * -> (* -> *) -> * -> *) where
  type VMap ReaderT = ContravariantT (Covariant1T (CovariantT (->)))
  vmap = ContravariantT $ \f1'
      -> Covariant1T $ \f2
      -> CovariantT $ \f3
      -> \body
      -> ReaderT $ \r'
      -> fmap f3 $ runNF f2 $ runReaderT body $ f1' r'

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
  type VMap StateT = InvariantT (Covariant1T (CovariantT (->)))
  vmap = InvariantT $ \(f1, f1')
      -> Covariant1T $ \f2
      -> CovariantT $ \f3
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

instance VFunctor Identity where
  type VMap Identity = CovariantT (->)
  vmap = CovariantT $ \f1
      -> \(Identity x1)
      -> Identity (f1 x1)

instance VFunctor (,) where
  type VMap (,) = CovariantT (CovariantT (->))
  vmap = CovariantT $ \f1
      -> CovariantT $ \f2
      -> \(x1,x2)
      -> (f1 x1, f2 x2)

instance VFunctor (,,) where
  type VMap (,,) = CovariantT (CovariantT (CovariantT (->)))
  vmap = CovariantT $ \f1
      -> CovariantT $ \f2
      -> CovariantT $ \f3
      -> \(x1,x2,x3)
      -> (f1 x1, f2 x2, f3 x3)

instance VFunctor (,,,) where
  type VMap (,,,) = CovariantT (CovariantT (CovariantT (CovariantT (->))))
  vmap = CovariantT $ \f1
      -> CovariantT $ \f2
      -> CovariantT $ \f3
      -> CovariantT $ \f4
      -> \(x1,x2,x3,x4)
      -> (f1 x1, f2 x2, f3 x3, f4 x4)

instance VFunctor (,,,,) where
  type VMap (,,,,) = CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (->)))))
  vmap = CovariantT $ \f1
      -> CovariantT $ \f2
      -> CovariantT $ \f3
      -> CovariantT $ \f4
      -> CovariantT $ \f5
      -> \(x1,x2,x3,x4,x5)
      -> (f1 x1, f2 x2, f3 x3, f4 x4, f5 x5)

instance VFunctor (,,,,,) where
  type VMap (,,,,,) = CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (->))))))
  vmap = CovariantT $ \f1
      -> CovariantT $ \f2
      -> CovariantT $ \f3
      -> CovariantT $ \f4
      -> CovariantT $ \f5
      -> CovariantT $ \f6
      -> \(x1,x2,x3,x4,x5,x6)
      -> (f1 x1, f2 x2, f3 x3, f4 x4, f5 x5, f6 x6)

instance VFunctor (,,,,,,) where
  type VMap (,,,,,,) = CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (->)))))))
  vmap = CovariantT $ \f1
      -> CovariantT $ \f2
      -> CovariantT $ \f3
      -> CovariantT $ \f4
      -> CovariantT $ \f5
      -> CovariantT $ \f6
      -> CovariantT $ \f7
      -> \(x1,x2,x3,x4,x5,x6,x7)
      -> (f1 x1, f2 x2, f3 x3, f4 x4, f5 x5, f6 x6, f7 x7)

instance VFunctor (,,,,,,,) where
  type VMap (,,,,,,,) = CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (->))))))))
  vmap = CovariantT $ \f1
      -> CovariantT $ \f2
      -> CovariantT $ \f3
      -> CovariantT $ \f4
      -> CovariantT $ \f5
      -> CovariantT $ \f6
      -> CovariantT $ \f7
      -> CovariantT $ \f8
      -> \(x1,x2,x3,x4,x5,x6,x7,x8)
      -> (f1 x1, f2 x2, f3 x3, f4 x4, f5 x5, f6 x6, f7 x7, f8 x8)

instance VFunctor (,,,,,,,,) where
  type VMap (,,,,,,,,) = CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (->)))))))))
  vmap = CovariantT $ \f1
      -> CovariantT $ \f2
      -> CovariantT $ \f3
      -> CovariantT $ \f4
      -> CovariantT $ \f5
      -> CovariantT $ \f6
      -> CovariantT $ \f7
      -> CovariantT $ \f8
      -> CovariantT $ \f9
      -> \(x1,x2,x3,x4,x5,x6,x7,x8,x9)
      -> (f1 x1, f2 x2, f3 x3, f4 x4, f5 x5, f6 x6, f7 x7, f8 x8, f9 x9)

instance VFunctor (,,,,,,,,,) where
  type VMap (,,,,,,,,,) = CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (->))))))))))
  vmap = CovariantT $ \f1
      -> CovariantT $ \f2
      -> CovariantT $ \f3
      -> CovariantT $ \f4
      -> CovariantT $ \f5
      -> CovariantT $ \f6
      -> CovariantT $ \f7
      -> CovariantT $ \f8
      -> CovariantT $ \f9
      -> CovariantT $ \f10
      -> \(x1,x2,x3,x4,x5,x6,x7,x8,x9,x10)
      -> (f1 x1, f2 x2, f3 x3, f4 x4, f5 x5, f6 x6, f7 x7, f8 x8, f9 x9, f10 x10)

instance VFunctor (,,,,,,,,,,) where
  type VMap (,,,,,,,,,,) = CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (->)))))))))))
  vmap = CovariantT $ \f1
      -> CovariantT $ \f2
      -> CovariantT $ \f3
      -> CovariantT $ \f4
      -> CovariantT $ \f5
      -> CovariantT $ \f6
      -> CovariantT $ \f7
      -> CovariantT $ \f8
      -> CovariantT $ \f9
      -> CovariantT $ \f10
      -> CovariantT $ \f11
      -> \(x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11)
      -> (f1 x1, f2 x2, f3 x3, f4 x4, f5 x5, f6 x6, f7 x7, f8 x8, f9 x9, f10 x10, f11 x11)

instance VFunctor (,,,,,,,,,,,) where
  type VMap (,,,,,,,,,,,) = CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (->))))))))))))
  vmap = CovariantT $ \f1
      -> CovariantT $ \f2
      -> CovariantT $ \f3
      -> CovariantT $ \f4
      -> CovariantT $ \f5
      -> CovariantT $ \f6
      -> CovariantT $ \f7
      -> CovariantT $ \f8
      -> CovariantT $ \f9
      -> CovariantT $ \f10
      -> CovariantT $ \f11
      -> CovariantT $ \f12
      -> \(x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12)
      -> (f1 x1, f2 x2, f3 x3, f4 x4, f5 x5, f6 x6, f7 x7, f8 x8, f9 x9, f10 x10, f11 x11, f12 x12)

instance VFunctor (,,,,,,,,,,,,) where
  type VMap (,,,,,,,,,,,,) = CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (->)))))))))))))
  vmap = CovariantT $ \f1
      -> CovariantT $ \f2
      -> CovariantT $ \f3
      -> CovariantT $ \f4
      -> CovariantT $ \f5
      -> CovariantT $ \f6
      -> CovariantT $ \f7
      -> CovariantT $ \f8
      -> CovariantT $ \f9
      -> CovariantT $ \f10
      -> CovariantT $ \f11
      -> CovariantT $ \f12
      -> CovariantT $ \f13
      -> \(x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13)
      -> (f1 x1, f2 x2, f3 x3, f4 x4, f5 x5, f6 x6, f7 x7, f8 x8, f9 x9, f10 x10, f11 x11, f12 x12, f13 x13)

instance VFunctor (,,,,,,,,,,,,,) where
  type VMap (,,,,,,,,,,,,,) = CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (->))))))))))))))
  vmap = CovariantT $ \f1
      -> CovariantT $ \f2
      -> CovariantT $ \f3
      -> CovariantT $ \f4
      -> CovariantT $ \f5
      -> CovariantT $ \f6
      -> CovariantT $ \f7
      -> CovariantT $ \f8
      -> CovariantT $ \f9
      -> CovariantT $ \f10
      -> CovariantT $ \f11
      -> CovariantT $ \f12
      -> CovariantT $ \f13
      -> CovariantT $ \f14
      -> \(x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14)
      -> (f1 x1, f2 x2, f3 x3, f4 x4, f5 x5, f6 x6, f7 x7, f8 x8, f9 x9, f10 x10, f11 x11, f12 x12, f13 x13, f14 x14)

instance VFunctor (,,,,,,,,,,,,,,) where
  type VMap (,,,,,,,,,,,,,,) = CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (->)))))))))))))))
  vmap = CovariantT $ \f1
      -> CovariantT $ \f2
      -> CovariantT $ \f3
      -> CovariantT $ \f4
      -> CovariantT $ \f5
      -> CovariantT $ \f6
      -> CovariantT $ \f7
      -> CovariantT $ \f8
      -> CovariantT $ \f9
      -> CovariantT $ \f10
      -> CovariantT $ \f11
      -> CovariantT $ \f12
      -> CovariantT $ \f13
      -> CovariantT $ \f14
      -> CovariantT $ \f15
      -> \(x1,x2,x3,x4,x5,x6,x7,x8,x9,x10,x11,x12,x13,x14,x15)
      -> (f1 x1, f2 x2, f3 x3, f4 x4, f5 x5, f6 x6, f7 x7, f8 x8, f9 x9, f10 x10, f11 x11, f12 x12, f13 x13, f14 x14, f15 x15)

-- 16-tuples don't even have a Show instance, so we don't bother with an VFunctor instance either
