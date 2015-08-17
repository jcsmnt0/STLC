module Monad

partial forever : Monad m => m a -> m a
forever x = do
  _ <- x
  forever x

partial until : Monad m => (a -> Bool) -> m a -> m a
until f x = do
  x' <- x
  if f x' then return x' else forever x

join : Monad m => m (m a) -> m a
join = (>>= id)
