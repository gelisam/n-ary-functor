{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, PolyKinds, RankNTypes, TypeFamilies, TypeOperators, UndecidableInstances, UnicodeSyntax #-}
module NAryFunctor where

import Control.Arrow
import Control.Monad.Trans.Reader
import Control.Monad.Trans.State
import Control.Monad.Trans.Writer
import Control.Natural
import Data.Bifunctor
import Data.Functor.Const
import Data.Functor.Identity

-- $setup
-- >>> import Control.Monad.Trans.Class
-- >>> let (<&>) = flip (<$>)


-- |
-- A generalization of 'Functor', 'Bifunctor', 'Trifunctor', etc., but also a
-- generalization of 'Contravariant', 'Invariant', 'Profunctor', and even
-- 'MFunctor'. We can 'nmap' over all three type parameters of 'StateT' even
-- though they have different kinds and different variances.
--
-- * @(NFunctor f, VarianceStack f ~ CovariantT (->)@ is equivalent to @Functor f@.
-- * @(NFunctor f, VarianceStack f ~ CovariantT (CovariantT (->))@ is equivalent to
--   @Bifunctor f@.
-- * @(NFunctor f, VarianceStack f ~ ContravariantT (->)@ is equivalent to
--   @Contravariant f@.
-- * @(NFunctor f, VarianceStack f ~ InvariantT (->)@ is equivalent to
--   @Invariant f@.
-- * @(NFunctor f, VarianceStack f ~ ContravariantT (CovariantT (->))@ is equivalent
--   to @Profunctor f@.
-- * @(NFunctor f, VarianceStack f ~ Covariant1T (->))@ is similar to @MFunctor f@
--   or @Functor1 f@. Different versions of this typeclass put different
--   constraints on the input and output type parameters.
--
-- Let's look at the generalization of 'Functor' to n-ary functors first.
--
-- Example usage:
--
-- >>> nmap <#> (+1) $ Identity 0
-- Identity 1
--
-- >>> nmap <#> (+1) <#> (+2) $ (0, 0)
-- (1,2)
--
-- >>> nmap <#> (+1) <#> (+2) <#> (+3) $ (0, 0, 0)
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
-- >   type VarianceStack (,,) = CovariantT (CovariantT (CovariantT (->)))
-- >   nmap = CovariantT $ \f1
-- >       -> CovariantT $ \f2
-- >       -> CovariantT $ \f3
-- >       -> \(x1,x2,x3)
-- >       -> (f1 x1, f2 x2, f3 x3)
--
-- The associated type 'VarianceStack' specifies the variance of all the type
-- parameters using a stack of 'VarianceTransformer's ending with @(->)@. When
-- generalizing 'Functor' to an n-ary functor, all the type parameters are
-- covariant, and so we need to compose @n@ copies of the 'CovariantT' variance
-- transformer.
--
-- Let's consider the case @n = 2@. With two copies of 'CovariantT', the type of
-- 'nmap' is @CovariantT (CovariantT (->)) f f@, so when calling 'nmap', we need
-- to unwrap two layers of 'CovariantT'. The unwrapping function is named
-- @(\<\#\>)@, not @runCovariantT@, so the call @(nmap \<\#\> g) \<\#\> h@ is
-- unwrapping the two 'CovariantT' layers in order to produce a value in
-- @(->)@, namely a function of type @f a1 a2 -> f b1 b2@. In those two calls,
-- the type of @(\<\#\>)@ gets specialized as follows:
--
-- > (<#>) :: CovariantT (CovariantT (->)) f f
-- >       -> (a1 -> b1)
-- >       -> CovariantT (->) (f a1) (f b1)
-- >
-- > (<#>) :: CovariantT (->) (f a1) (f b1)
-- >       -> (a2 -> b2)
-- >       -> (->) (f a1 a2) (f a2 b2)
--
-- Next, let's see how this approach allows us to 'nmap' over all three type
-- parameters of 'StateT'. This time, the instance looks like this:
--
-- > instance NFunctor StateT where
-- >   type VarianceStack StateT = InvariantT (Covariant1T (CovariantT (->)))
-- >   nmap = InvariantT $ \(f1, f1')
-- >       -> Covariant1T $ \f2
-- >       -> CovariantT $ \f3
-- >       -> \body
-- >       -> StateT $ \s'
-- >       -> fmap (f3 *** f1) $ unwrapNT f2 $ runStateT body $ f1' s'
--
-- 'StateT' has three type parameters, 's', 'm', and 'a'. We will thus need to
-- compose three variance transformers. Since a 'StateT' computation both
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
-- and add a @1@ to the name of the variance transformer. To 'nmap' over all
-- three type parameters, the three variance transformers we must combine are
-- thus 'InvariantT', 'Covariant1T', and 'CovariantT', and so @StateT@'s
-- 'VarianceStack' is @InvariantT (Covariant1T (CovariantT (->)))@.
-- Each of these is unwrapped via a different infix operator:
-- @nmap \<\#\>/\>\#\< (f1,f1') \<\#\#\> f2 \<\#\> f3@, whose types get
-- specialized as follows:
--
-- > (<#>/>#<) :: InvariantT (Covariant1T (CovariantT (->))) StateT StateT
-- >           -> (s -> t, t -> s)
-- >           -> Covariant1T (CovariantT (->)) (StateT s) (StateT t)
-- >
-- > (<##>) :: (Functor m, Functor n)
-- >        => Covariant1T (CovariantT (->)) (StateT s) (StateT t)
-- >        -> m :~> n
-- >        -> CovariantT (->) (StateT s m) (StateT t n)
-- >
-- > (<#>) :: CovariantT (->) (StateT s m) (StateT t n)
-- >       -> (a -> b)
-- >       -> StateT s m a -> StateT t n b
--
-- Since 'nmap' can have so many different types, it's a bit hard to state the
-- laws in general, but it's the obvious ones: using 'id' everywhere yields
-- 'id', and two composed 'nmap's is equivalent to a single 'nmap' in which the
-- functions are composed; covariantly or contravariantly, as appropriate. For
-- example, the laws for @StateT@'s 'nmap' are:
--
-- > nmap <#>/>#< (id,id) <##> id <#> id = id
-- > (nmap <#>/>#< (f1,f1') <##> f2 <#> f3) . (nmap <#>/>#< (g1,g1') <##> g2 <#> g3) = nmap <#>/>#< (f1 . g1, g1' . f1') <##> (f2 . g2) <#> (f3 . g3)
--
-- Note that it is /not/ possible to write an instance for a partially-applied
-- type; for example, it is not possible to write an @NFunctor ((,) a)@
-- instance corresponding to the @Functor ((,) a)@ instance. If there are some
-- type parameters which cannot be mapped, simply use 'NonvariantT' to leave
-- them untouched. Here is what the @(,)@ instance would look like if we did
-- not know how to map its first type parameter.
--
-- > instance NFunctor (,) where
-- >   type VarianceStack (,) = NonvariantT (CovariantT (->))
-- >   nmap = NonvariantT
-- >        $ CovariantT$ \f2
-- >        $ \(x1, x2)
-- >       -> (x1, f2 x2)
--
-- The infix unwrapping function for 'NonvariantT' type parameters is '-#-':
--
-- >>> nmap -#- () <#> (+2) $ (0, 0)
-- (0,2)
--
-- In fact, '-#-' can be used to leave any type parameter unchanged.
--
-- >>> nmap -#- () -#- () <#> (+3) -#- () $ (0, 0, 0, 0)
-- (0,0,3,0)
--
-- And the first few @-#- ()@s can be omitted.
--
-- >>> nmap -#- () <#> (+3) -#- () $ (0, 0, 0, 0)
-- (0,0,3,0)
-- >>> nmap <#> (+3) -#- () $ (0, 0, 0, 0)
-- (0,0,3,0)
--
-- That is, by writing a @NFunctor (,)@ instance, you automatically get the
-- instances for @NFunctor ((,) a)@ and @NFunctor (,) a b@ for free. The
-- bold @NFunctor f => NFunctor (f a)@ instance which gives you those instances
-- for free is the reason you can't write an @NFunctor ((->) a)@ instance: it
-- would overlap with our bold instance.
class NFunctor (f :: k) where
  type VarianceStack f :: k -> k -> *
  nmap :: VarianceStack f f f


-- |
-- This library uses a stack of 'VarianceTransformer's to indicate the variance
-- of each type parameter. Each transformer in the stack specifies the variance
-- of one type parameter, and wraps an inner stack specifying the variance of
-- the remaining type parameters, until we reach @(->)@, the base of the stack.
--
-- Each 'VarianceTransformer' is eliminated by an infix function, such as
-- @(\<\#\>)@. This function takes a stack on the left, and its right argument
-- has whatever type is necessary in order to map over the corresponding
-- type parameter; for covariant type parameters, it will be a function of type
-- @(a1 -> b1)@, for contravariant type parameters, it will be a function of
-- type @(b1 -> a1)@, for invariant type parameters, it will be a pair of
-- functions @(a1 -> b1, b1 -> a2)@, etc.
--
-- The @(-#-)@ method witnesses the fact that regardless of the variance of a
-- given type parameter, there is always an identity-like argument which can be
-- passed as the second argument which will cause that type parameter to be
-- left unchanged. It takes a stack on the left, and its right argument is
-- simply '()'.
class VarianceTransformer (t :: (k -> k -> *)
                             -> (k1 -> k) -> (k1 -> k) -> *)
                          (a :: k1)
                          where
  (-#-) :: t inner f g -> () -> inner (f a) (g a)


newtype CovariantT to f f' = CovariantT
  { (<#>) :: forall a a'
           . (a -> a')
          -> f a `to` f' a'
  }

instance VarianceTransformer CovariantT a where
  t -#- () = t <#> id


newtype ContravariantT to f f' = ContravariantT
  { (>#<) :: forall a a'
           . (a' -> a)
          -> f a `to` f' a'
  }

instance VarianceTransformer ContravariantT a where
  t -#- () = t >#< id


newtype InvariantT to f f' = InvariantT
  { (<#>/>#<) :: forall a a'
               . (a -> a', a' -> a)
              -> f a `to` f' a'
  }

instance VarianceTransformer InvariantT a where
  t -#- () = t <#>/>#< (id, id)


newtype NonvariantT to f f' = NonvariantT
  { unNonvariant :: forall a a'. (a ~ a')
                 => f a `to` f' a'
  }

instance VarianceTransformer NonvariantT a where
  t -#- () = unNonvariant t


newtype PhantomvariantT to f f' = PhantomvariantT
  { (👻#👻) :: forall a a'
             . ()
            -> f a `to` f' a'
  }

instance VarianceTransformer PhantomvariantT a where
  t -#- () = t 👻#👻 ()



newtype Covariant1T to f f' = Covariant1T
  { (<##>) :: forall m m'. (Functor m, Functor m')
           => m :~> m'
           -> f m `to` f' m'
  }

instance Functor m
      => VarianceTransformer Covariant1T m where
  t -#- () = t <##> NT id


newtype Contravariant1T to f f' = Contravariant1T
  { (>##<) :: forall m m'. (Functor m, Functor m')
           => m' :~> m
           -> f m `to` f' m'
  }

instance Functor m
      => VarianceTransformer Contravariant1T m where
  t -#- () = t >##< NT id


newtype Invariant1T to f f' = Invariant1T
  { (<##>/>##<) :: forall m m'. (Functor m, Functor m')
                => (m :~> m', m' :~> m)
                -> f m `to` f' m'
  }

instance Functor m
      => VarianceTransformer Invariant1T m where
  t -#- () = t <##>/>##< (NT id, NT id)



-- |
-- A bold instance! We should be suspicious of any instance for @f a@, because
-- it is likely to overlap with other instances. For instance, what if we want
-- to define an @NFunctor ((->) a)@ instance corresponding to the @Functor ((->) a)@
-- instance?
--
-- I claim that we will never want to write such an instance; we will always
-- prefer to write the @NFunctor (->)@ instance instead, and to have the
-- @NFunctor ((->) a)@ derived from the @NFunctor (->)@ instance via this bold
-- instance. If you really can't find a way to map over a type parameter, use
-- 'NonvariantT' to skip over it.
instance ( NFunctor f
         , VarianceStack f ~ t inner
         , VarianceTransformer t a
         )
      => NFunctor (f a) where
  --type VarianceStack (f a) = inner
  type VarianceStack (f a) = VarianceTransformer'Inner (VarianceStack f)
  nmap = nmap -#- ()

-- We can't write @type VarianceStack (f a) = inner@, ghc complains that 'inner' is not
-- in scope, so we instead have to write this type family which extracts 'inner'
-- from @VarianceStack f@.
type family VarianceTransformer'Inner f where
  VarianceTransformer'Inner (t inner) = inner



-- Instances

-- |
-- >>> nmap          <#> (+2) $ Right (0::Int)
-- Right 2
-- >>> nmap <#> (+1) <#> (+2) $ Left (0::Int)
-- Left 1
--
-- >>> nmap          -#- ()   $ Right (0::Int)
-- Right 0
-- >>> nmap <#> (+1) -#- ()   $ Left (0::Int)
-- Left 1
-- >>> nmap -#- ()   <#> (+2) $ Right (0::Int)
-- Right 2
-- >>> nmap -#- ()   -#- ()   $ Left (0::Int)
-- Left 0
instance NFunctor Either where
  type VarianceStack Either = CovariantT (CovariantT (->))
  nmap = CovariantT $ \f1
      -> CovariantT $ \f2
      -> bimap f1 f2

-- |
-- >>> let intToInt       =                            succ
-- >>> let intToString    = nmap            <#> show $ succ
-- >>> let stringToString = nmap >#< length <#> show $ succ
-- >>> intToInt 3
-- 4
-- >>> intToString 3
-- "4"
-- >>> stringToString "foo"
-- "4"
--
-- >>> let intToInt    = nmap            -#- ()   $ succ
-- >>> let stringToInt = nmap >#< length -#- ()   $ succ
-- >>> let intToString = nmap -#- ()     <#> show $ succ
-- >>> let intToInt'   = nmap -#- ()     -#- ()   $ succ
-- >>> intToInt 3
-- 4
-- >>> stringToInt "foo"
-- 4
-- >>> intToString 3
-- "4"
-- >>> intToInt' 3
-- 4
instance NFunctor (->) where
  type VarianceStack (->) = ContravariantT (CovariantT (->))
  nmap = ContravariantT $ \f1'
      -> CovariantT $ \f2
      -> \g
      -> f2 . g . f1'

-- |
-- >>> let readerIntIdentityInt    = ((`div` 2) <$> ask) >>= lift . Identity
-- >>> let readerIntIdentityString = nmap                                         <#> show $ readerIntIdentityInt
-- >>> let readerIntMaybeString    = nmap            <##> NT (Just . runIdentity) <#> show $ readerIntIdentityInt
-- >>> let readerStringMaybeString = nmap >#< length <##> NT (Just . runIdentity) <#> show $ readerIntIdentityInt
-- >>> runReaderT readerIntIdentityInt 4
-- Identity 2
-- >>> runReaderT readerIntIdentityString 4
-- Identity "2"
-- >>> runReaderT readerIntMaybeString 4
-- Just "2"
-- >>> runReaderT readerStringMaybeString "four"
-- Just "2"
--
-- >>> let readerIntIdentityInt'      = nmap                                         -#- ()   $ readerIntIdentityInt
-- >>> let readerIntMaybeInt          = nmap            <##> NT (Just . runIdentity) -#- ()   $ readerIntIdentityInt
-- >>> let readerIntIdentityString    = nmap            -#-  ()                      <#> show $ readerIntIdentityInt
-- >>> let readerIntIdentityInt''     = nmap            -#-  ()                      -#- ()   $ readerIntIdentityInt
-- >>> let readerStringMaybeInt       = nmap >#< length <##> NT (Just . runIdentity) -#- ()   $ readerIntIdentityInt
-- >>> let readerStringIdentityString = nmap >#< length -#-  ()                      <#> show $ readerIntIdentityInt
-- >>> let readerStringIdentityInt    = nmap >#< length -#-  ()                      -#- ()   $ readerIntIdentityInt
-- >>> let readerIntMaybeString       = nmap -#- ()     <##> NT (Just . runIdentity) <#> show $ readerIntIdentityInt
-- >>> let readerIntMaybeInt'         = nmap -#- ()     <##> NT (Just . runIdentity) -#- ()   $ readerIntIdentityInt
-- >>> let readerIntIdentityString'   = nmap -#- ()     -#-  ()                      <#> show $ readerIntIdentityInt
-- >>> let readerIntIdentityInt'''    = nmap -#- ()     -#-  ()                      -#- ()   $ readerIntIdentityInt
-- >>> runReaderT readerIntIdentityInt' 4
-- Identity 2
-- >>> runReaderT readerIntMaybeInt 4
-- Just 2
-- >>> runReaderT readerIntIdentityString 4
-- Identity "2"
-- >>> runReaderT readerIntIdentityInt'' 4
-- Identity 2
-- >>> runReaderT readerStringMaybeInt "four"
-- Just 2
-- >>> runReaderT readerStringIdentityString "four"
-- Identity "2"
-- >>> runReaderT readerStringIdentityInt "four"
-- Identity 2
-- >>> runReaderT readerIntMaybeString 4
-- Just "2"
-- >>> runReaderT readerIntMaybeInt' 4
-- Just 2
-- >>> runReaderT readerIntIdentityString' 4
-- Identity "2"
-- >>> runReaderT readerIntIdentityInt''' 4
-- Identity 2
instance NFunctor (ReaderT :: * -> (* -> *) -> * -> *) where
  type VarianceStack ReaderT = ContravariantT (Covariant1T (CovariantT (->)))
  nmap = ContravariantT $ \f1'
      -> Covariant1T $ \f2
      -> CovariantT $ \f3
      -> \body
      -> ReaderT $ \r'
      -> fmap f3 $ unwrapNT f2 $ runReaderT body $ f1' r'

-- |
-- >>> let stateIntIdentityInt    = ((`div` 2) <$> get) >>= lift . Identity
-- >>> let stateIntIdentityString = nmap                                                                   <#> show $ stateIntIdentityInt
-- >>> let stateIntMaybeString    = nmap                                      <##> NT (Just . runIdentity) <#> show $ stateIntIdentityInt
-- >>> let stateStringMaybeString = nmap <#>/>#< (flip replicate '.', length) <##> NT (Just . runIdentity) <#> show $ stateIntIdentityInt
-- >>> runStateT stateIntIdentityInt 4
-- Identity (2,4)
-- >>> runStateT stateIntIdentityString 4
-- Identity ("2",4)
-- >>> runStateT stateIntMaybeString 4
-- Just ("2",4)
-- >>> runStateT stateStringMaybeString "four"
-- Just ("2","....")
--
-- >>> let stateIntIdentityInt'      = nmap                                                                           -#- ()   $ stateIntIdentityInt
-- >>> let stateIntMaybeInt          = nmap                                              <##> NT (Just . runIdentity) -#- ()   $ stateIntIdentityInt
-- >>> let stateIntIdentityString    = nmap                                              -#-  ()                      <#> show $ stateIntIdentityInt
-- >>> let stateIntIdentityInt''     = nmap                                              -#-  ()                      -#- ()   $ stateIntIdentityInt
-- >>> let stateStringMaybeInt       = nmap <#>/>#< (flip replicate '.', length) <##> NT (Just . runIdentity) -#- ()   $ stateIntIdentityInt
-- >>> let stateStringIdentityString = nmap <#>/>#< (flip replicate '.', length) -#-  ()                      <#> show $ stateIntIdentityInt
-- >>> let stateStringIdentityInt    = nmap <#>/>#< (flip replicate '.', length) -#-  ()                      -#- ()   $ stateIntIdentityInt
-- >>> let stateIntMaybeString       = nmap -#-     ()                           <##> NT (Just . runIdentity) <#> show $ stateIntIdentityInt
-- >>> let stateIntMaybeInt'         = nmap -#-     ()                           <##> NT (Just . runIdentity) -#- ()   $ stateIntIdentityInt
-- >>> let stateIntIdentityString'   = nmap -#-     ()                           -#-  ()                      <#> show $ stateIntIdentityInt
-- >>> let stateIntIdentityInt'''    = nmap -#-     ()                           -#-  ()                      -#- ()   $ stateIntIdentityInt
-- >>> runStateT stateIntIdentityInt' 4
-- Identity (2,4)
-- >>> runStateT stateIntMaybeInt 4
-- Just (2,4)
-- >>> runStateT stateIntIdentityString 4
-- Identity ("2",4)
-- >>> runStateT stateIntIdentityInt'' 4
-- Identity (2,4)
-- >>> runStateT stateStringMaybeInt "four"
-- Just (2,"....")
-- >>> runStateT stateStringIdentityString "four"
-- Identity ("2","....")
-- >>> runStateT stateStringIdentityInt "four"
-- Identity (2,"....")
-- >>> runStateT stateIntMaybeString 4
-- Just ("2",4)
-- >>> runStateT stateIntMaybeInt' 4
-- Just (2,4)
-- >>> runStateT stateIntIdentityString' 4
-- Identity ("2",4)
-- >>> runStateT stateIntIdentityInt''' 4
-- Identity (2,4)
instance NFunctor StateT where
  type VarianceStack StateT = InvariantT (Covariant1T (CovariantT (->)))
  nmap = InvariantT $ \(f1, f1')
      -> Covariant1T $ \f2
      -> CovariantT $ \f3
      -> \body
      -> StateT $ \s'
      -> fmap (f3 *** f1) $ unwrapNT f2 $ runStateT body $ f1' s'

-- |
-- >>> let writerIntIdentityInt    = do {tell [4]; lift $ Identity 2}
-- >>> let writerIntIdentityString = nmap                                       <#> show $ writerIntIdentityInt
-- >>> let writerIntMaybeString    = nmap          <##> NT (Just . runIdentity) <#> show $ writerIntIdentityInt
-- >>> let writerStringMaybeString = nmap <#> show <##> NT (Just . runIdentity) <#> show $ writerIntIdentityInt
-- >>> runWriterT writerIntIdentityInt
-- Identity (2,[4])
-- >>> runWriterT writerIntIdentityString
-- Identity ("2",[4])
-- >>> runWriterT writerIntMaybeString
-- Just ("2",[4])
-- >>> runWriterT writerStringMaybeString
-- Just ("2","[4]")
--
-- >>> let writerIntIdentityInt'      = nmap                                                                    -#- ()   $ writerIntIdentityInt
-- >>> let writerIntMaybeInt          = nmap                                       <##> NT (Just . runIdentity) -#- ()   $ writerIntIdentityInt
-- >>> let writerIntIdentityString    = nmap                                       -#-  ()                      <#> show $ writerIntIdentityInt
-- >>> let writerIntIdentityInt''     = nmap                                       -#-  ()                      -#- ()   $ writerIntIdentityInt
-- >>> let writerStringMaybeInt       = nmap <#> show <##> NT (Just . runIdentity) -#- ()   $ writerIntIdentityInt
-- >>> let writerStringIdentityString = nmap <#> show -#-  ()                      <#> show $ writerIntIdentityInt
-- >>> let writerStringIdentityInt    = nmap <#> show -#-  ()                      -#- ()   $ writerIntIdentityInt
-- >>> let writerIntMaybeString       = nmap -#- ()   <##> NT (Just . runIdentity) <#> show $ writerIntIdentityInt
-- >>> let writerIntMaybeInt'         = nmap -#- ()   <##> NT (Just . runIdentity) -#- ()   $ writerIntIdentityInt
-- >>> let writerIntIdentityString'   = nmap -#- ()   -#-  ()                      <#> show $ writerIntIdentityInt
-- >>> let writerIntIdentityInt'''    = nmap -#- ()   -#-  ()                      -#- ()   $ writerIntIdentityInt
-- >>> runWriterT writerIntIdentityInt'
-- Identity (2,[4])
-- >>> runWriterT writerIntMaybeInt
-- Just (2,[4])
-- >>> runWriterT writerIntIdentityString
-- Identity ("2",[4])
-- >>> runWriterT writerIntIdentityInt''
-- Identity (2,[4])
-- >>> runWriterT writerStringMaybeInt
-- Just (2,"[4]")
-- >>> runWriterT writerStringIdentityString
-- Identity ("2","[4]")
-- >>> runWriterT writerStringIdentityInt
-- Identity (2,"[4]")
-- >>> runWriterT writerIntMaybeString
-- Just ("2",[4])
-- >>> runWriterT writerIntMaybeInt'
-- Just (2,[4])
-- >>> runWriterT writerIntIdentityString'
-- Identity ("2",[4])
-- >>> runWriterT writerIntIdentityInt'''
-- Identity (2,[4])
instance NFunctor WriterT where
  type VarianceStack WriterT = CovariantT (Covariant1T (CovariantT (->)))
  nmap = CovariantT $ \f1
      -> Covariant1T $ \f2
      -> CovariantT $ \f3
      -> \body
      -> WriterT
       $ fmap (f3 *** f1) $ unwrapNT f2 $ runWriterT body

-- |
-- >>> let myConst = Const "foo" :: Const String Double
-- >>> (nmap            👻#👻 () $ myConst) <&> length
-- Const "foo"
-- >>> (nmap <#> length 👻#👻 () $ myConst) <&> length
-- Const 3
--
-- >>> (nmap            -#-   () $ myConst)
-- Const "foo"
-- >>> (nmap <#> length -#-   () $ myConst)
-- Const 3
-- >>> (nmap -#- ()     👻#👻 () $ myConst) <&> length
-- Const "foo"
-- >>> (nmap -#- ()     -#-   () $ myConst)
-- Const "foo"
instance NFunctor Const where
  type VarianceStack Const = CovariantT (PhantomvariantT (->))
  nmap = CovariantT $ \f1
      -> PhantomvariantT $ \()
      -> \(Const a1)
      -> Const (f1 a1)


-- |
-- For kind @*@, 'nmap' must be the identity function. If 'Bifunctor' and
-- 'Functor' correspond to binary and unary functors, this corresponds to a
-- "nullary" functor.
--
-- >>> nmap ()
-- ()
instance NFunctor () where
  type VarianceStack () = (->)
  nmap = id

instance NFunctor Identity where
  type VarianceStack Identity = CovariantT (->)
  nmap = CovariantT $ \f1
      -> \(Identity x1)
      -> Identity (f1 x1)

instance NFunctor (,) where
  type VarianceStack (,) = CovariantT (CovariantT (->))
  nmap = CovariantT $ \f1
      -> CovariantT $ \f2
      -> \(x1,x2)
      -> (f1 x1, f2 x2)

instance NFunctor (,,) where
  type VarianceStack (,,) = CovariantT (CovariantT (CovariantT (->)))
  nmap = CovariantT $ \f1
      -> CovariantT $ \f2
      -> CovariantT $ \f3
      -> \(x1,x2,x3)
      -> (f1 x1, f2 x2, f3 x3)

instance NFunctor (,,,) where
  type VarianceStack (,,,) = CovariantT (CovariantT (CovariantT (CovariantT (->))))
  nmap = CovariantT $ \f1
      -> CovariantT $ \f2
      -> CovariantT $ \f3
      -> CovariantT $ \f4
      -> \(x1,x2,x3,x4)
      -> (f1 x1, f2 x2, f3 x3, f4 x4)

instance NFunctor (,,,,) where
  type VarianceStack (,,,,) = CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (->)))))
  nmap = CovariantT $ \f1
      -> CovariantT $ \f2
      -> CovariantT $ \f3
      -> CovariantT $ \f4
      -> CovariantT $ \f5
      -> \(x1,x2,x3,x4,x5)
      -> (f1 x1, f2 x2, f3 x3, f4 x4, f5 x5)

instance NFunctor (,,,,,) where
  type VarianceStack (,,,,,) = CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (->))))))
  nmap = CovariantT $ \f1
      -> CovariantT $ \f2
      -> CovariantT $ \f3
      -> CovariantT $ \f4
      -> CovariantT $ \f5
      -> CovariantT $ \f6
      -> \(x1,x2,x3,x4,x5,x6)
      -> (f1 x1, f2 x2, f3 x3, f4 x4, f5 x5, f6 x6)

instance NFunctor (,,,,,,) where
  type VarianceStack (,,,,,,) = CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (->)))))))
  nmap = CovariantT $ \f1
      -> CovariantT $ \f2
      -> CovariantT $ \f3
      -> CovariantT $ \f4
      -> CovariantT $ \f5
      -> CovariantT $ \f6
      -> CovariantT $ \f7
      -> \(x1,x2,x3,x4,x5,x6,x7)
      -> (f1 x1, f2 x2, f3 x3, f4 x4, f5 x5, f6 x6, f7 x7)

instance NFunctor (,,,,,,,) where
  type VarianceStack (,,,,,,,) = CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (->))))))))
  nmap = CovariantT $ \f1
      -> CovariantT $ \f2
      -> CovariantT $ \f3
      -> CovariantT $ \f4
      -> CovariantT $ \f5
      -> CovariantT $ \f6
      -> CovariantT $ \f7
      -> CovariantT $ \f8
      -> \(x1,x2,x3,x4,x5,x6,x7,x8)
      -> (f1 x1, f2 x2, f3 x3, f4 x4, f5 x5, f6 x6, f7 x7, f8 x8)

instance NFunctor (,,,,,,,,) where
  type VarianceStack (,,,,,,,,) = CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (->)))))))))
  nmap = CovariantT $ \f1
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

instance NFunctor (,,,,,,,,,) where
  type VarianceStack (,,,,,,,,,) = CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (->))))))))))
  nmap = CovariantT $ \f1
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

instance NFunctor (,,,,,,,,,,) where
  type VarianceStack (,,,,,,,,,,) = CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (->)))))))))))
  nmap = CovariantT $ \f1
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

instance NFunctor (,,,,,,,,,,,) where
  type VarianceStack (,,,,,,,,,,,) = CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (->))))))))))))
  nmap = CovariantT $ \f1
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

instance NFunctor (,,,,,,,,,,,,) where
  type VarianceStack (,,,,,,,,,,,,) = CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (->)))))))))))))
  nmap = CovariantT $ \f1
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

instance NFunctor (,,,,,,,,,,,,,) where
  type VarianceStack (,,,,,,,,,,,,,) = CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (->))))))))))))))
  nmap = CovariantT $ \f1
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

instance NFunctor (,,,,,,,,,,,,,,) where
  type VarianceStack (,,,,,,,,,,,,,,) = CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (->)))))))))))))))
  nmap = CovariantT $ \f1
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

-- 16-tuples don't even have a Show instance, so we don't bother with an NFunctor instance either
