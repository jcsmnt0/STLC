module Monad

covering forever : Monad m => m a -> m a
forever x = x *> forever x

covering until : Monad m => (a -> Bool) -> m a -> m a
until f x = do
  x' <- x
  if f x' then return x' else until f x

%default total

join : Monad m => m (m a) -> m a
join = (>>= id)

(>>) : Monad m => m a -> m b -> m b
x >> y = x >>= const y
