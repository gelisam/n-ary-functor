{-# LANGUAGE RankNTypes #-}
module NAryFunctor.NT where

import Prelude hiding (id, (.))
import Control.Category

newtype NT m m' = NT
  { runNT :: forall a. m a -> m' a
  }

instance Category NT where
  id = NT id
  NT f . NT g = NT (f . g)
