module Ex

%default total

data Ex : (a -> Type) -> Type where
  E : b x -> Ex b

fst : Ex {a = a} b -> a
fst (E {x = x} _) = x

snd : (ex : Ex b) -> b (fst ex)
snd (E y) = y
