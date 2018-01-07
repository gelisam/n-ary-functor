# N-ary Functors

[![Build Status](https://travis-ci.org/gelisam/n-ary-functor.svg?branch=master)](https://travis-ci.org/gelisam/n-ary-functor)

[`Functor`](https://hackage.haskell.org/package/base-4.10.1.0/docs/Prelude.html#t:Functor) and [`Bifunctor`](https://hackage.haskell.org/package/base-4.10.1.0/docs/Data-Bifunctor.html#t:Bifunctor) are both in `base`, but what about `Trifunctor`? `Quadrifunctor`? There must be a better solution than creating an infinite tower of typeclasses. Here's the API I managed to implement:

    > nmap <#> (+1) <#> (+2) $ (0, 0)
    (1,2)

    > nmap <#> (+1) <#> (+2) <#> (+3) $ (0, 0, 0)
    (1,2,3)

    > nmap <#> (+1) <#> (+2) <#> (+3) <#> (+4) $ (0, 0, 0, 0)
    (1,2,3,4)

For more details, see the [documentation](https://hackage.haskell.org/package/n-ary-functor-0.1.0.0/docs/NAryFunctor.html) and the [blog post](http://gelisam.blogspot.ca/2017/12/n-ary-functors.html).
