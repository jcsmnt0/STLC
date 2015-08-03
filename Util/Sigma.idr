module Sigma

namespace Simple
  uncurry :
    {c : a -> b -> Type} ->
    ((x : a) -> (y : b) -> c x y) ->
    (pr : (a, b)) ->
    c (fst pr) (snd pr)
  uncurry f (x, y) = f x y

namespace Dependent
  fst : {b : a -> Type} -> (x : a ** b x) -> a
  fst (x ** _) = x

  snd : {b : a -> Type} -> (pr : (x : a ** b x)) -> b (fst pr)
  snd (_ ** y) = y

  uncurry :
    {b : a -> Type} ->
    {c : (x : a) -> b x -> Type} ->
    ((x : a) -> (y : b x) -> c x y) ->
    (pr : (x ** b x)) ->
    c (fst pr) (snd pr)
  uncurry f (x ** y) = f x y
