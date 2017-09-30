module Monad

%access export

covering forever : Monad m => m a -> m a
forever x = x *> forever x

covering until : Monad m => (a -> Bool) -> m a -> m a
until f x = do
  x' <- x
  if f x' then pure x' else until f x

%default total

(>>) : Monad m => m a -> m b -> m b
x >> y = x >>= const y
