{-# LANGUAGE Trustworthy #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE ScopedTypeVariables #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Control.Monad.PolyCont
-- Copyright   :  (c) 2018 David Feuer
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  David.Feuer@gmail.com
-- Stability   :  experimental
-- Portability :  non-portable
--
-- Continuation monads.
--
-- Delimited continuation operators are taken from Kenichi Asai and Oleg
-- Kiselyov's tutorial at CW 2011, \"Introduction to programming with
-- shift and reset\" (<http://okmij.org/ftp/continuations/#tutorial>).
--
-- This module is based on "Control.Monad.Trans.Cont" in the transformers
-- package.
--
-- Unlike the transformers package, this package defines 'Cont' as a
-- first-class type. This is because the current lack of poly-kinded
-- @newtype@s makes it impossible to define 'Cont' in terms of
-- @"Control.Monad.Trans.PolyCont".'Control.Monad.Trans.PolyCont.ContT'@
-- in any particularly nice way.
--
-----------------------------------------------------------------------------

module Control.Monad.PolyCont (
    -- * The Cont monad
    Cont (..),
    cont,
    evalCont,
    mapCont,
    withCont,
    -- ** Delimited continuations
    reset, shift,
    callCC,
  ) where

import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import Data.Functor.Identity

import Control.Applicative
import Control.Monad.Fail
import GHC.Exts (TYPE)
import Data.Kind

import qualified Control.Monad.Cont.Class as Class
import Prelude hiding (fail)

{- |
Continuation monad.
@Cont r a@ is a CPS ("continuation-passing style") computation that produces an
intermediate result of type @a@ within a CPS computation whose final result type
is @r@.

The @return@ function simply creates a continuation which passes the value on.

The @>>=@ operator adds the bound function into the continuation chain.
-}
newtype Cont (r :: TYPE rep) a = Cont
  { runCont :: (a -> r) -> r }

-- | Construct a continuation-passing computation from a function.
-- (The inverse of 'runCont')
cont :: forall a (r :: TYPE rep). ((a -> r) -> r) -> Cont r a
cont f = Cont f
{-# INLINE cont #-}

-- | The result of running a CPS computation with the identity as the
-- final continuation.
--
-- * @'evalCont' ('return' x) = x@
evalCont :: Cont r r -> r
evalCont m = runCont m id
{-# INLINE evalCont #-}

-- | Apply a function to transform the result of a continuation-passing
-- computation.
--
-- * @'runCont' ('mapCont' f m) = f . 'runCont' m@
mapCont :: (r -> r) -> Cont r a -> Cont r a
mapCont f m = Cont $ f . runCont m
{-# INLINE mapCont #-}

-- | Apply a function to transform the continuation passed to a CPS
-- computation.
--
-- * @'runCont' ('withCont' f m) = 'runCont' m . f@
withCont :: forall (r :: TYPE rep) a b. ((b -> r) -> (a -> r)) -> Cont r a -> Cont r b
withCont f m = Cont $ \br -> runCont m (f br)
{-# INLINE withCont #-}

-- | @'reset' m@ delimits the continuation of any 'shift' inside @m@.
--
-- * @'reset' ('return' m) = 'return' m@
--
reset :: forall r (r' :: TYPE rep). Cont r r -> Cont r' r
reset m = Cont $ \rr' -> rr' $ runCont m id
{-# INLINE reset #-}

-- | @'shift' f@ captures the continuation up to the nearest enclosing
-- 'reset' and passes it to @f@:
--
-- * @'reset' ('shift' f >>= k) = 'reset' (f ('evalCont' . k))@
--
shift :: ((a -> r) -> Cont r r) -> Cont r a
shift f = Cont $ \ar -> evalCont (f ar)
{-# INLINE shift #-}

instance Functor (Cont (r :: TYPE rep)) where
    fmap f m = Cont $ \ c -> runCont m (\x -> c (f x))
    {-# INLINE fmap #-}

instance Applicative (Cont (r :: TYPE rep)) where
    pure x  = Cont ($ x)
    {-# INLINE pure #-}
    f <*> v = Cont $ \ c -> runCont f $ \ g -> runCont v (\x -> c (g x))
    {-# INLINE (<*>) #-}
    m *> k = m >>= \_ -> k
    {-# INLINE (*>) #-}

instance Monad (Cont (r :: TYPE rep)) where
    m >>= k  = Cont $ \ c -> runCont m (\ x -> runCont (k x) c)
    {-# INLINE (>>=) #-}

instance Class.MonadCont (Cont r) where
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
callCC :: forall (r :: TYPE rep) a b. ((a -> Cont r b) -> Cont r a) -> Cont r a
callCC f = Cont $ \ c -> runCont (f (\ x -> Cont $ \ _ -> c x)) c
{-# INLINE callCC #-}
