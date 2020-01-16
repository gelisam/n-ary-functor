## Next in 1.0

* Breaking change: all instances now need to specify the variance of all type
  parameters.
* Breaking change: instances of the form `NFunctor (f a)` are no longer
  allowed. Instead, write `NFunctor f` and use `NonvariantT` to indicate that
  `a` cannot be mapped.
* `NFunctor` is now even more general: in addition to generalizing `Functor`,
  `Bifunctor`, `Trifunctor`, etc., it now also generalizes `Contravariant`,
  `Invariant`, `Profunctor`, and even `MFunctor` aka `Functor1`!
* Introducing new infix operators corresponding to each variance. `(<#>)` is
  still used for covariant type parameters, so after updating the instances,
  all the call sites which were using the 0.1 API should still work. `(>#<)` is
  used for contravariant type parameters, `(<#>/>#<)` is used for invariant
  type parameters, which can be mapped given both a covariant and a
  contravariant function, and `(👻#👻)` is used for phantom type parameters.
* Introducing the `(-#-)` operator, which support, which can be used instead of
  any other operator in order to leave the corresponding type parameter
  untouched.
* Introducing support for mapping over type parameters of kind `* -> *` using
  natural transformations. The corresponding infix operators have two hashes:
  the covariant operator is `(<##>)`, the contravariant operator is `(>##<)`,
  etc.
* Introducing the `VarianceTransformer` typeclass, via which you can add
  support for other variances and other kinds.
* It is no longer needed (nor allowed) to write both an `NFunctor Either`
  instance and an `NFunctor (Either a)` instance corresponding to `Either`'s
  `Bifunctor` and `Functor` instances. Instead, the `NFunctor (Either a)`
  instance is derived from the `NFunctor Either` instance.

## New in 0.1.0.0

* Initial release of the `NFunctor` typeclass
