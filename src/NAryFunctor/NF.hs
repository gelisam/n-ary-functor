{-# LANGUAGE RankNTypes #-}
module NAryFunctor.NF where

import Prelude hiding (id, (.))
import Control.Category

newtype NF m m' = NF
  { runNF :: forall a. m a -> m' a
  }

instance Category NF where
  id = NF id
  NF f . NF g = NF (f . g)
