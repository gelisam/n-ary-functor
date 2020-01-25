# N-ary Functors [![Hackage](https://img.shields.io/hackage/v/n-ary-functor.svg)](https://hackage.haskell.org/package/n-ary-functor) [![Build Status](https://secure.travis-ci.org/gelisam/n-ary-functor.png?branch=master)](https://travis-ci.org/gelisam/n-ary-functor)

## Using existing instances

[`Functor`](https://hackage.haskell.org/package/base-4.10.1.0/docs/Prelude.html#t:Functor) and [`Bifunctor`](https://hackage.haskell.org/package/base-4.10.1.0/docs/Data-Bifunctor.html#t:Bifunctor) are both in `base`, but what about `Trifunctor`? `Quadrifunctor`? There must be a better solution than creating an infinite tower of typeclasses. Here's the API I managed to implement:

```haskell
> nmap <#> (+1) <#> (+2) $ (0, 0)
(1,2)

> nmap <#> (+1) <#> (+2) <#> (+3) $ (0, 0, 0)
(1,2,3)

> nmap <#> (+1) <#> (+2) <#> (+3) <#> (+4) $ (0, 0, 0, 0)
(1,2,3,4)
```

What about [`Contravariant`](https://www.stackage.org/haddock/lts-14.20/base-4.12.0.0/Data-Functor-Contravariant.html#t:Contravariant) and [`Profunctor`](https://www.stackage.org/haddock/lts-14.20/profunctors-5.3/Data-Profunctor.html#t:Profunctor)? No need to define `Bicontravariant` nor `Noobfunctor`, the `NFunctor` typeclass supports contravariant type-parameters too!

```haskell
> let intToInt       =                            succ
> let intToString    = nmap            <#> show $ succ
> let stringToString = nmap >#< length <#> show $ succ
> intToInt 3
4
> intToString 3
"4"
> stringToString "foo"
"4"
```

As the examples above demonstrate, n-ary-functor has an equivalent for both the `Functor ((->) a)` instance and the `Profunctor (->)` instance. Even better: when writing your own instance, you only need to define an `NFunctor (->)` instance, and the `NFunctor ((->) a)` instance will be derived for you. `NFunctor ((->) a b)` too, but that's less useful since that `nmap` is just the identity function.

That's not all! Consider a type like `StateT s m a`. The last type parameter is covariant, but what about the first two? Well, `s -> m (a, s)` has both positive and negative occurences of `s`, so you need both an `s -> t` and a `t -> s` function in order to turn a `StateT s m a` into a `StateT t m a`. And what about `m`? You need a natural transformation `forall a. m a -> n a`. Yes, n-ary-functor supports these too!

```haskell
> let stateIntIdentityInt    = ((`div` 2) <$> get) >>= lift . Identity
> let stateStringMaybeString = nmap
                       <#>/>#< (flip replicate '.', length)  -- (s -> t, t -> s)
                          <##> NT (Just . runIdentity)       -- NT (forall a. m a -> n a)
                           <#> show                          -- a -> b
                             $ stateIntIdentityInt
> runStateT stateIntIdentityInt 4
Identity (2,4)
> runStateT stateStringMaybeString "four"
Just ("2","....")
```

Notice how even in such a complicated case, no type annotations are needed, as n-ary-functor is written with type inference in mind.


## Defining your own instance

When defining an instance of `NFunctor`, you need to specify the variance of every type parameter using a "variance stack" ending with `(->)`. Here is the instance for `(,,)`, whose three type parameters are covariant:

```haskell
instance NFunctor (,,) where
  type VarianceStack (,,) = CovariantT (CovariantT (CovariantT (->)))
  nmap = CovariantT $ \f1
      -> CovariantT $ \f2
      -> CovariantT $ \f3
      -> \(x1,x2,x3)
      -> (f1 x1, f2 x2, f3 x3)
```

Its `nmap` then receives 3 functions, which it applies to the 3 components of the 3-tuple.

Here is a more complicated instance, that of `StateT`:

```haskell
instance NFunctor StateT where
  type VarianceStack StateT = InvariantT (Covariant1T (CovariantT (->)))
  nmap = InvariantT  $ \(f1, f1')
      -> Covariant1T $ \f2
      -> CovariantT  $ \f3
      -> \body
      -> StateT $ \s'
      -> fmap (f3 *** f1) $ unwrapNT f2 $ runStateT body $ f1' s'
```

The `s` type parameter is "invariant", a standard but confusing name which does _not_ mean that the parameter cannot vary, but rather that we need both an `s -> t` and a `t -> s`. The `m` parameter is covariant, but for a type parameter of kind `* -> *`, so we follow the [convention](http://hackage.haskell.org/package/base-4.11.1.0/docs/Data-Functor-Classes.html) and add a `1` to the name of the variance transformer, hence `Covariant1T`.


## Defining your own variance transformer

We've seen plenty of strange variances already and n-ary-functor provides stranger ones still (can you guess what the `👻#👻` operator does?), but if your type parameters vary in an even more unusual way, you can define your own variance transformer. Here's what the definition of `CovariantT` looks like:

```haskell
newtype CovariantT to f g = CovariantT
  { (<#>) :: forall a b
           . (a -> b)
          -> f a `to` g b
  }
```

One thing which is unusual in that newtype definition is that instead of naming the eliminator `unCovariantT`, we give it the infix name `(<#>)`. See [this blog post](http://gelisam.blogspot.com/2017/12/n-ary-functors.html#ergonomics) for more details on that aspect.

Let's look at the type wrapped by the newtype. `to` is the rest of the variance stack, so in the simplest case, `to` is just `(->)`, in which case the wrapped type is `(a -> b) -> f a -> g b`, which is really close to the type of `fmap`. The reason we produce a `g b` instead of an `f b` is because previous type parameters might already be fmapped; for example, in `nmap <#> show <#> show $ (0, 0)`, the overall transformation has type `(,) Int Int -> (,) String String`, so from the point of view of the second `(<#>)`, `f` is `(,) Int` and `g` is `(,) String`.

One last thing is that variance transformers must implement the `VarianceTransformer` typeclass. It simply ensures that there exists a neutral argument, in this case `id`, which doesn't change the type parameter at all.

```haskell
instance VarianceTransformer CovariantT a where
  t -#- () = t <#> id
```


### Flavor example

A concrete situation in which you'd want to define your own variance transformer is if you have a DataKind type parameter which corresponds to a number of other types via type families.

```haskell
import qualified Data.ByteString      as Strict
import qualified Data.ByteString.Lazy as Lazy
import qualified Data.Text            as Strict
import qualified Data.Text.Lazy       as Lazy

data Flavor
  = Strict
  | Lazy

type family ByteString (flavor :: Flavor) :: * where
  ByteString 'Lazy   = Lazy.ByteString
  ByteString 'Strict = Strict.ByteString

type family Text (flavor :: Flavor) :: * where
  Text 'Lazy   = Lazy.Text
  Text 'Strict = Strict.Text

data File (flavor :: Flavor) = File
  { name     :: Text flavor
  , size     :: Int
  , contents :: ByteString flavor
  }
```

In order to convert a `File 'Lazy` to a `File 'Strict`, we need to map both the underlying `Text 'Lazy` to a `Text 'Strict` and the underlying `ByteString 'Lazy` to a `ByteString 'Strict`. So those are exactly the two functions our custom variance transformer will ask for:

```haskell
newtype FlavorvariantT to f g = FlavorvariantT
  { (😋#😋) :: forall flavor1 flavor2
           . ( ByteString flavor1 -> ByteString flavor2
             , Text       flavor1 -> Text       flavor2
             )
          -> f flavor1 `to` g flavor2
  }

instance VarianceTransformer FlavorvariantT a where
  t -#- () = t 😋#😋 (id, id)
```

We can now implement our `NFunctor File` instance by specifying that its `flavor` type parameter is flavorvariant.

```haskell
instance NFunctor File where
  type VarianceStack File = FlavorvariantT (->)
  nmap = FlavorvariantT $ \(f, g)
      -> \(File n s c)
      -> File (g n) s (f c)
```
