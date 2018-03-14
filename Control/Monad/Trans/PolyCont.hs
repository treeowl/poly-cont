{-# LANGUAGE Trustworthy #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Control.Monad.Trans.PolyCont
-- Copyright   :  (c) David Feuer 2018
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :
-- Stability   :  experimental
-- Portability :  non-portable
--
-- Continuation monads.
--
-- Delimited continuation operators are taken from Kenichi Asai and Oleg
-- Kiselyov's tutorial at CW 2011, \"Introduction to programming with
-- shift and reset\" (<http://okmij.org/ftp/continuations/#tutorial>).
--
-- Based on "Control.Monad.Trans.Cont" in the transformers package.
--
-----------------------------------------------------------------------------

module Control.Monad.Trans.PolyCont (
    -- * The ContT monad transformer
    ContT(..),
    evalContT,
    mapContT,
    withContT,
    callCC,
    -- ** Delimited continuations
    resetT, shiftT,
    -- * Lifting other operations
    liftLocal,
  ) where

import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import Data.Functor.Identity

import Control.Applicative
import Control.Monad.Fail
import GHC.Exts (TYPE)
import Data.Type.Equality (type (~~))
import Control.Monad.Reader.Class
import Control.Monad.State.Class
import qualified Control.Monad.Cont.Class as Class
import Prelude hiding (fail)

-- | The continuation monad transformer.
-- Can be used to add continuation handling to any type constructor:
-- the 'Monad' instance and most of the operations do not require @m@
-- to be a monad.
--
-- 'ContT' is not a functor on the category of monads, and many operations
-- cannot be lifted through it.
newtype ContT (r :: k) (m :: k -> TYPE rep) a =
  ContT { runContT :: (a -> m r) -> m r }

-- | The result of running a CPS computation with 'return' as the
-- final continuation.
--
-- * @'evalContT' ('lift' m) = m@
evalContT :: Monad m => ContT r m r -> m r
evalContT m = runContT m return
{-# INLINE evalContT #-}

-- | Apply a function to transform the result of a continuation-passing
-- computation.  This has a more restricted type than the @map@ operations
-- for other monad transformers, because 'ContT' does not define a functor
-- in the category of monads.
--
-- * @'runContT' ('mapContT' f m) = f . 'runContT' m@
mapContT :: (m r -> m r) -> ContT r m a -> ContT r m a
mapContT f m = ContT $ f . runContT m
{-# INLINE mapContT #-}

-- | Apply a function to transform the continuation passed to a CPS
-- computation.
--
-- * @'runContT' ('withContT' f m) = 'runContT' m . f@
withContT :: forall (r :: k) (m :: k -> TYPE rep) a b.
             ((b -> m r) -> (a -> m r)) -> ContT r m a -> ContT r m b
withContT f m = ContT $ \x -> runContT m (f x)
{-# INLINE withContT #-}

instance Functor (ContT r (m :: k -> TYPE rep)) where
    fmap f m = ContT $ \ c -> runContT m (\x -> c (f x))
    {-# INLINE fmap #-}

instance Applicative (ContT r (m :: k -> TYPE rep)) where
    pure x  = ContT ($ x)
    {-# INLINE pure #-}
    f <*> v = ContT $ \ c -> runContT f $ \ g -> runContT v (\x -> c (g x))
    {-# INLINE (<*>) #-}
    m *> k = m >>= \_ -> k
    {-# INLINE (*>) #-}

instance Monad (ContT r (m :: k -> TYPE rep)) where
    m >>= k  = ContT $ \ c -> runContT m (\ x -> runContT (k x) c)
    {-# INLINE (>>=) #-}

instance (m ~~ m', MonadFail m') => MonadFail (ContT r (m :: k -> TYPE rep)) where
    fail msg = ContT $ \ _ -> fail msg
    {-# INLINE fail #-}

instance MonadTrans (ContT r) where
    lift m = ContT (m >>=)
    {-# INLINE lift #-}

instance (m ~~ m', MonadIO m') => MonadIO (ContT r (m :: k -> TYPE rep)) where
    liftIO = lift . liftIO
    {-# INLINE liftIO #-}

instance (m ~~ m', MonadReader r' m')
  => MonadReader r' (ContT r (m :: k -> TYPE rep)) where
  ask = lift ask
  local = liftLocal ask local
  reader = lift . reader

instance (m ~~ m', MonadState s m')
  => MonadState s (ContT r (m :: k -> TYPE rep)) where
  get = lift get
  put = lift . put
  state = lift . state

instance Class.MonadCont (ContT r m) where
  callCC = callCC

-- | @callCC@ (call-with-current-continuation) calls its argument
-- function, passing it the current continuation.  It provides
-- an escape continuation mechanism for use with continuation
-- monads.  Escape continuations one allow to abort the current
-- computation and return a value immediately.  They achieve
-- a similar effect to 'Control.Monad.Trans.Except.throwE'
-- and 'Control.Monad.Trans.Except.catchE' within an
-- 'Control.Monad.Trans.Except.ExceptT' monad.  The advantage of this
-- function over calling 'return' is that it makes the continuation
-- explicit, allowing more flexibility and better control.
--
-- The standard idiom used with @callCC@ is to provide a lambda-expression
-- to name the continuation. Then calling the named continuation anywhere
-- within its scope will escape from the computation, even if it is many
-- layers deep within nested computations.
callCC :: forall (r :: k) (m :: k -> TYPE rep) a b.
  ((a -> ContT r m b) -> ContT r m a) -> ContT r m a
callCC f = ContT $ \ c -> runContT (f (\ x -> ContT $ \ _ -> c x)) c
{-# INLINE callCC #-}

-- | @'resetT' m@ delimits the continuation of any 'shiftT' inside @m@.
--
-- * @'resetT' ('lift' m) = 'lift' m@
--
resetT :: Monad m => ContT r m r -> ContT r' m r
resetT = lift . evalContT
{-# INLINE resetT #-}

-- | @'shiftT' f@ captures the continuation up to the nearest enclosing
-- 'resetT' and passes it to @f@:
--
-- * @'resetT' ('shiftT' f >>= k) = 'resetT' (f ('evalContT' . k))@
--
shiftT :: Monad m => ((a -> m r) -> ContT r m r) -> ContT r m a
shiftT f = ContT (evalContT . f)
{-# INLINE shiftT #-}

-- | @'liftLocal' ask local@ yields a @local@ function for @'ContT' r m@.
liftLocal :: Monad m => m r' -> ((r' -> r') -> m r -> m r) ->
    (r' -> r') -> ContT r m a -> ContT r m a
liftLocal ask local f m = ContT $ \ c -> do
    r <- ask
    local f (runContT m (local (const r) . c))
{-# INLINE liftLocal #-}
