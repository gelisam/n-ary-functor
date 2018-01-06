# N-ary Functors

[`Functor`](https://hackage.haskell.org/package/base-4.10.1.0/docs/Prelude.html#t:Functor) and [`Bifunctor`](https://hackage.haskell.org/package/base-4.10.1.0/docs/Data-Bifunctor.html#t:Bifunctor) are both in `base`, but what about `Trifunctor`? `Quadrifunctor`? There must be a better solution than creating an infinite tower of typeclasses. Here's the API I managed to implement:

    > nmap <#> (+1) <#> (+2) $ (0, 0)
    (1,2)

    > nmap <#> (+1) <#> (+2) <#> (+3) $ (0, 0, 0)
    (1,2,3)

    > nmap <#> (+1) <#> (+2) <#> (+3) <#> (+4) $ (0, 0, 0, 0)
    (1,2,3,4)

For more details, see the documentation and the [blog post](http://gelisam.blogspot.ca/2017/12/n-ary-functors.html).
