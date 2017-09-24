module Ex

%default total
%access export

infixr 0 $$

||| Lightweight syntax for dependent pairs whose first value can usually be inferred:
||| Ex b <=> (x : _ ** b _)
||| E y <=> (_ ** y)
||| (could probably be a syntax definition instead?)
public export
data Ex : (a -> Type) -> Type where
  E : b x -> Ex b

fst : Ex {a = a} b -> a
fst (E {x = x} _) = x

snd : (ex : Ex b) -> b (fst ex)
snd (E y) = y
