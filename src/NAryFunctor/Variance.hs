{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, PolyKinds, RankNTypes, TypeFamilies, TypeOperators, UndecidableInstances, UnicodeSyntax #-}
module NAryFunctor.Variance where

import Control.Arrow
import Control.Monad.Trans.Reader
import Control.Monad.Trans.State
import Control.Monad.Trans.Writer
import Data.Bifunctor
import Data.Functor.Const
import Data.Functor.Identity

import NAryFunctor.NT

-- $setup
-- >>> import Control.Monad.Trans.Class


-- |
-- A generalization of 'Functor', 'Bifunctor', 'Trifunctor', etc., but also a
-- generalization of 'Contravariant', 'Invariant', 'Profunctor', and 'MFunctor'.
-- We can 'nmap' over all three type parameters of 'StateT' even though they
-- have different kinds and different variances.
--
-- Let's look at the generalization of 'Functor' to n-ary functors first.
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
-- >   type Variance (,,) = CovariantT (CovariantT (CovariantT (->)))
-- >   nmap = ...
--
-- The associated type 'Variance' specifies variance of all the type parameters
-- using a stack of 'MappingTransformer' ending with @(->)@. When generalizing
-- 'Functor' to an n-ary functor, all the type parameters are covariant, and
-- so we need to compose @n@ copies of the 'CovariantT' mapping transformer.
--
-- Let's consider the case @n = 2@. With two copies of 'CovariantT', the type of
-- 'nmap' is @CovariantT (CovariantT (->)) f f@, so when calling 'nmap', we need
-- to unwrap two layers of 'CovariantT'. The unwrapping function is named
-- @(\<\#\>)@, not @runCovariantT@, so the call @nmap \<\#\> g \<\#\> h@ is
-- unwrapping the two 'CovariantT' layers in order to produce a value in the
-- base @(->)@ mapping, namely a function of type @f a b -> f a' b'@. In those
-- two calls, the type of @(\<\#\>)@ gets specialized as follows:
--
-- > (<#>) :: CovariantT (CovariantT (->)) f f
-- >       -> (a -> a')
-- >       -> CovariantT (->) (f a) (f a')
-- >
-- > (<#>) :: CovariantT (->) (f a) (f a')
-- >       -> (b -> b')
-- >       -> f a b -> f a' b'
--
-- Next, let's see how this approach allows us to 'nmap' over all three type
-- parameters of 'StateT'. This time, the instance looks like this:
--
-- > instance NFunctor StateT where
-- >   type Variance StateT = InvariantT (Covariant1T (CovariantT (->)))
-- >   nmap = ...
--
-- 'StateT' has three type parameters, 's', 'm', and 'a'. We will thus need to
-- compose three mapping transformers. Since a 'StateT' computation both
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
-- and add a @1@ to the name of the mapping transformer. To 'nmap' over all
-- three type parameters, the three mapping transformers we must combine are
-- thus 'InvariantT', 'Covariant1T', and 'CovariantT', and so the type of
-- @StateT@'s 'nmap' is @InvariantT (Covariant1T (CovariantT (->)))@.
-- Each of these is unwrapped via a different infix operator:
-- @nmap \<\#\>/\>\#\< (f,f') \<\#\#\> NT g \<\#\> h@, whose types get
-- specialized as follows:
--
-- > (<#>/>#<) :: InvariantT (Covariant1T (CovariantT (->))) StateT StateT
-- >           -> (s -> s', s' -> s)
-- >           -> Covariant1T (CovariantT (->)) (StateT s) (StateT s')
-- >
-- > (<##>) :: (Functor m, Functor m')
-- >        => Covariant1T (CovariantT (->)) (StateT s) (StateT s')
-- >        -> NT m m'
-- >        -> CovariantT (->) (StateT s m) (StateT s' m')
-- >
-- > (<#>) :: CovariantT (->) (StateT s m) (StateT s' m')
-- >       -> (a -> a')
-- >       -> StateT s m a -> StateT s' m' a'
--
-- Since 'nmap' can have so many different types, it's a bit hard to state the
-- laws in general, but it's the obvious ones: using 'id' everywhere yields
-- 'id', and two composed 'nmap's is equivalent to a single 'nmap' in which the
-- functions are composed; covariantly or contravariantly, as appropriate. For
-- example, the laws for @StateT@'s 'nmap' are:
--
-- > nmap <#>/>#< (id,id) <##> id <#> id = id
-- > (nmap <#>/>#< (f1,f1') <##> f2 <#> f3) . (nmap <#>/>#< (g1,g1') <##> g2 <#> g3) = nmap <#>/>#< (f1 . g1, g1' . f1') <##> (f2 . g2) <#> (f3 . g3)
class NFunctor (f :: k) where
  type Variance f :: k -> k -> *
  nmap :: Variance f f f


-- |
-- A mapping function is a function such as @fmap@ or @bimap@, which takes as
-- input one function over each type parameter of 'f' and converts them into a
-- function over 'f' values. The functions over the type parameters do not need
-- to be covariant.
--
-- > fmap :: (a -> b) -> f a -> f b
-- > bimap :: (a1 -> b1) -> (a2 -> b2) -> f a1 a2 -> f b1 b2
-- > dimap :: (b1 -> a1) -> (a2 -> b2) -> f a1 a2 -> f b1 b2
--
-- These three functions all map an 'f' to an 'f', but in general, a mapping
-- function may map an 'f' to a 'g'. So 'bimap' is both a mapping function from
-- 'f' to 'f', from @f a1@ to @f b1@ and from @f a1 a2@ to @f b1 b2@.
--
-- Partially applying a mapping function results in another mapping function:
--
-- > fmap :: (a -> b) -> f a -> f b
-- > fmap not :: f Bool -> f Bool
--
-- > dimap :: (b1 -> a1) -> (a2 -> b2) -> f a1 a2 -> f b1 b2
-- > dimap not :: (a2 -> b2) -> f Bool a2 -> f Bool b2
-- > dimap not (++ "!") :: f Bool String -> f Bool String
--
-- A mapping transformer expresses the relation between a mapping function
-- and its partially-applied variants. For example, the type of 'fmap' is
-- equivalent to the newtype @CovariantT (->) f f@, which indicates that the
-- type of the fully-applied variant has the form @(->) (f _) (f _)@.
-- Similarly, the type of 'dimap' is equivalent to
-- @ContravariantT (CovariantT (->)) f f@, which indicates that the type of the
-- partially-applied variant has the form @Covariant (->) (f _) (f _)@ (or
-- equivalently @(a -> b) -> f _ a -> f _ b@), which in turn indicates that the
-- type of the fully-applied variant has the form @(->) (f _ _) (f _ _)@. In
-- general, @SomethingT inner f g@ is equivalent to a type which, if
-- partially-applied, would be equivalent to a type of the form
-- @inner (f _) (g _)@.
--
-- As the 'dimap' example indicates, those mapping transformers are typically
-- part of a stack, just like monad transformers. Monad transformer stacks end
-- with 'Identity', mapping transformer stacks end with @(->)@.
--
-- The @(-#-)@ method witnesses the fact that regardless of the variance of a
-- given type parameter, it is always possible to leave that type parameter
-- alone by partially-applying the mapping function to 'id' or something
-- equivalent.
class MappingTransformer (t :: (k -> k -> *)
                            -> (k1 -> k) -> (k1 -> k) -> *)
                         (a :: k1)
                         where
  (-#-) :: t inner f g -> () -> inner (f a) (g a)


newtype CovariantT to f f' = CovariantT
  { (<#>) :: forall a a'
           . (a -> a')
          -> f a `to` f' a'
  }

instance MappingTransformer CovariantT a where
  t -#- () = t <#> id


newtype ContravariantT to f f' = ContravariantT
  { (>#<) :: forall a a'
           . (a' -> a)
          -> f a `to` f' a'
  }

instance MappingTransformer ContravariantT a where
  t -#- () = t >#< id


newtype InvariantT to f f' = InvariantT
  { (<#>/>#<) :: forall a a'
               . (a -> a', a' -> a)
              -> f a `to` f' a'
  }

instance MappingTransformer InvariantT a where
  t -#- () = t <#>/>#< (id, id)


newtype NonvariantT to f f' = NonvariantT
  { unNonvariant :: forall a a'. (a ~ a')
                 => f a `to` f' a'
  }

instance MappingTransformer NonvariantT a where
  t -#- () = unNonvariant t


newtype PhantomvariantT to f f' = PhantomvariantT
  { (👻#👻) :: forall a a'
             . ()
            -> f a `to` f' a'
  }

instance MappingTransformer PhantomvariantT a where
  t -#- () = t 👻#👻 ()



newtype Covariant1T to f f' = Covariant1T
  { (<##>) :: forall m m'. (Functor m, Functor m')
           => NT m m'
           -> f m `to` f' m'
  }

instance Functor m
      => MappingTransformer Covariant1T m where
  t -#- () = t <##> NT id


newtype Contravariant1T to f f' = Contravariant1T
  { (>##<) :: forall m m'. (Functor m, Functor m')
           => NT m' m
           -> f m `to` f' m'
  }

instance Functor m
      => MappingTransformer Contravariant1T m where
  t -#- () = t >##< NT id


newtype Invariant1T to f f' = Invariant1T
  { (<##>/>##<) :: forall m m'. (Functor m, Functor m')
                => (NT m m', NT m' m)
                -> f m `to` f' m'
  }

instance Functor m
      => MappingTransformer Invariant1T m where
  t -#- () = t <##>/>##< (NT id, NT id)



-- |
-- A bold instance! We should be suspicious of any instance for @f a@, because
-- it is likely to overlap with other instances. For instance, what if we want
-- to define a @NFunctor ((->) a)@ instance corresponding to the @Functor ((->) a)@
-- instance?
--
-- I claim that we will never want to write such an instance; we will always
-- prefer to write the @NFunctor (->)@ instance instead, and to have the
-- @NFunctor ((->) a)@ derived from the @NFunctor (->)@ instance via this bold
-- instance. If you really can't find a way to transform a type parameter, use
-- 'NonvariantT' to skip over it.

instance ( NFunctor f
         , Variance f ~ t inner
         , MappingTransformer t a
         )
      => NFunctor (f a) where
  --type Variance (f a) = inner
  type Variance (f a) = MappingTransformer'Inner (Variance f)
  nmap = nmap -#- ()

-- We can't write @type Variance (f a) = inner@, ghc complains that 'inner' is not
-- in scope, so we instead have to write this type family which extracts 'inner'
-- from @Variance f@.
type family MappingTransformer'Inner f where
  MappingTransformer'Inner (t inner) = inner





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
  type Variance Either = CovariantT (CovariantT (->))
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
  type Variance (->) = ContravariantT (CovariantT (->))
  nmap = ContravariantT $ \f1'
      -> CovariantT $ \f2
      -> \g
      -> f2 . g . f1'

instance NFunctor NT where
  type Variance NT = Contravariant1T (Covariant1T (->))
  nmap = Contravariant1T $ \(NT f1')
      -> Covariant1T $ \(NT f2)
      -> \(NT g)
      -> NT (f2 . g . f1')

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
  type Variance ReaderT = ContravariantT (Covariant1T (CovariantT (->)))
  nmap = ContravariantT $ \f1'
      -> Covariant1T $ \f2
      -> CovariantT $ \f3
      -> \body
      -> ReaderT $ \r'
      -> fmap f3 $ runNT f2 $ runReaderT body $ f1' r'

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
  type Variance StateT = InvariantT (Covariant1T (CovariantT (->)))
  nmap = InvariantT $ \(f1, f1')
      -> Covariant1T $ \f2
      -> CovariantT $ \f3
      -> \body
      -> StateT $ \s'
      -> fmap (f3 *** f1) $ runNT f2 $ runStateT body $ f1' s'

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
  type Variance WriterT = CovariantT (Covariant1T (CovariantT (->)))
  nmap = CovariantT $ \f1
      -> Covariant1T $ \f2
      -> CovariantT $ \f3
      -> \body
      -> WriterT
       $ fmap (f3 *** f1) $ runNT f2 $ runWriterT body


-- |
-- For kind @*@, 'nmap' must be the identity function. If 'Bifunctor' and
-- 'Functor' correspond to binary and unary functors, this corresponds to a
-- "nullary" functor.
--
-- >>> nmap ()
-- ()
instance NFunctor () where
  type Variance () = (->)
  nmap = id

instance NFunctor Identity where
  type Variance Identity = CovariantT (->)
  nmap = CovariantT $ \f1
      -> \(Identity x1)
      -> Identity (f1 x1)

instance NFunctor (,) where
  type Variance (,) = CovariantT (CovariantT (->))
  nmap = CovariantT $ \f1
      -> CovariantT $ \f2
      -> \(x1,x2)
      -> (f1 x1, f2 x2)

instance NFunctor (,,) where
  type Variance (,,) = CovariantT (CovariantT (CovariantT (->)))
  nmap = CovariantT $ \f1
      -> CovariantT $ \f2
      -> CovariantT $ \f3
      -> \(x1,x2,x3)
      -> (f1 x1, f2 x2, f3 x3)

instance NFunctor (,,,) where
  type Variance (,,,) = CovariantT (CovariantT (CovariantT (CovariantT (->))))
  nmap = CovariantT $ \f1
      -> CovariantT $ \f2
      -> CovariantT $ \f3
      -> CovariantT $ \f4
      -> \(x1,x2,x3,x4)
      -> (f1 x1, f2 x2, f3 x3, f4 x4)

instance NFunctor (,,,,) where
  type Variance (,,,,) = CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (->)))))
  nmap = CovariantT $ \f1
      -> CovariantT $ \f2
      -> CovariantT $ \f3
      -> CovariantT $ \f4
      -> CovariantT $ \f5
      -> \(x1,x2,x3,x4,x5)
      -> (f1 x1, f2 x2, f3 x3, f4 x4, f5 x5)

instance NFunctor (,,,,,) where
  type Variance (,,,,,) = CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (->))))))
  nmap = CovariantT $ \f1
      -> CovariantT $ \f2
      -> CovariantT $ \f3
      -> CovariantT $ \f4
      -> CovariantT $ \f5
      -> CovariantT $ \f6
      -> \(x1,x2,x3,x4,x5,x6)
      -> (f1 x1, f2 x2, f3 x3, f4 x4, f5 x5, f6 x6)

instance NFunctor (,,,,,,) where
  type Variance (,,,,,,) = CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (->)))))))
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
  type Variance (,,,,,,,) = CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (->))))))))
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
  type Variance (,,,,,,,,) = CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (->)))))))))
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
  type Variance (,,,,,,,,,) = CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (->))))))))))
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
  type Variance (,,,,,,,,,,) = CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (->)))))))))))
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
  type Variance (,,,,,,,,,,,) = CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (->))))))))))))
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
  type Variance (,,,,,,,,,,,,) = CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (->)))))))))))))
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
  type Variance (,,,,,,,,,,,,,) = CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (->))))))))))))))
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
  type Variance (,,,,,,,,,,,,,,) = CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (CovariantT (->)))))))))))))))
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
