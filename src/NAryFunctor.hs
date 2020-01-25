{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, PolyKinds, RankNTypes, TypeFamilies, TypeOperators, UndecidableInstances, UnicodeSyntax #-}
module NAryFunctor
  ( NFunctor(..)
  , VarianceTransformer(..)
  , CovariantT(..),     Covariant1T(..)
  , ContravariantT(..), Contravariant1T(..)
  , InvariantT(..),     Invariant1T(..)
  , NonvariantT(..)
  , PhantomvariantT(..)
  ) where

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
-- A generalization of 'Functor', 'Bifunctor', 'Contravariant', 'Profunctor', etc.
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
--
-- The associated type 'VarianceStack' specifies the variance of all the type
-- parameters using a stack of 'VarianceTransformer's ending with @(->)@.
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
-- Note that it is /not/ possible to write an instance for a partially-applied
-- type; for example, it is not possible to write an @NFunctor ((,,) a)@
-- instance corresponding to the @Functor ((,,) a)@ instance. Instead, the
-- @NFunctor ((,,) a)@ and @NFunctor ((,,) a b)@ instances are derived from the
-- above instance.
--
-- Laws:
--
-- > nmap <#>     id       = nmap -#- () = id
-- > nmap     >#< id       = nmap -#- () = id
-- > nmap <#>/>#< (id, id) = nmap -#- () = id
-- > ...
--
-- > nmap -#- () -#- () <#> f =
-- > nmap        -#- () <#> f =
-- > nmap               <#> f
--
-- > (nmap <#> f1 <#> f2) . (nmap <#> g1 <#> g2) = nmap <#> (f1 . g1) <#> (f2 . g2)
-- > (nmap >#< f1 >#< f2) . (nmap >#< g1 >#< g2) = nmap >#< (g1 . f1) >#< (g2 . f2)
-- > ...
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
-- @(\<\#\>)@. This function takes a stack on the left, and its second argument
-- has whatever type is necessary in order to map over the corresponding
-- type parameter; for covariant type parameters, it will be a function of type
-- @(a -> b)@, for contravariant type parameters, it will be a function of
-- type @(b -> a)@, for invariant type parameters, it will be a pair of
-- functions @(a -> b, b -> a)@, etc.
--
-- The @(-\#-)@ method witnesses the fact that regardless of the variance of a
-- given type parameter, there is always an identity-like argument which can be
-- passed as that second argument which will cause that type parameter to be
-- left unchanged. It takes a stack on the left, and its second argument is
-- simply @()@.
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


-- |
-- If you can't figure out how to map over a particular type parameter, use
-- this variance and we'll leave it alone. The corresponding infix operator is
-- @(-\#-)@.
newtype NonvariantT to f f' = NonvariantT
  { unNonvariant :: forall a a'. (a ~ a')
                 => f a `to` f' a'
  }

instance VarianceTransformer NonvariantT a where
  t -#- () = unNonvariant t


-- |
-- Phantom type parameters can be changed to any other type, no @a -> b@
-- function needed, so we only ask for a @()@. Use @(-\#-)@ in the common case
-- in which you don't want to change the phantom type, and @(👻#👻)@ in the
-- rare case in which you do want to change it.
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
-- I claim that you will never have to write such an instance; it will always
-- be possible to write the @NFunctor (->)@ instance instead, and to have the
-- @NFunctor ((->) a)@ derived from the @NFunctor (->)@ instance via this bold
-- instance. If you really can't find a way to map over a type parameter, use
-- 'NonvariantT' to skip over it.
instance ( NFunctor f
         , VarianceStack f ~ t inner
         , VarianceTransformer t a
         )
      => NFunctor (f a) where
  --type VarianceStack (f a) = inner
  type VarianceStack (f a) = VarianceStack'Tail (VarianceStack f)
  nmap = nmap -#- ()

-- We can't write @type VarianceStack (f a) = inner@, ghc complains that 'inner' is not
-- in scope, so we instead have to write this type family which extracts 'inner'
-- from @VarianceStack f@.
type family VarianceStack'Tail f where
  VarianceStack'Tail (t inner) = inner



-- Instances

-- $
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

-- $
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

-- $
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

-- $
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

-- $
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

-- $
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
