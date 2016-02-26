module Applicative

%default total

(*>) : Applicative m => m a -> m b -> m b
x *> y = [| const y x |]

(<*) : Applicative m => m a -> m b -> m a
x <* y = [| const x y |]
