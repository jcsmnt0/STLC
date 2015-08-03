module Util.Elem

import Data.Fin
import Data.Vect

import Util.Dec

toFin : {xs : Vect n a} -> Elem x xs -> Fin n
toFin Here = FZ
toFin (There i) = FS (toFin i)

fromFin : Fin n -> (xs : Vect n a) -> (x : a ** Elem x xs)
fromFin FZ (x :: xs) = (x ** Here)
fromFin (FS i) (_ :: xs) = let (x ** p) = fromFin i xs in (x ** There p)

iso : {xs : Vect n a} -> (p : Elem x xs) -> (ys : Vect n b) -> (y : b ** Elem y ys)
iso Here (_ :: _) = (_ ** Here)
iso (There p) (_ :: ys) = let (_ ** q) = iso p ys in (_ ** There q)

extend : {b : a -> Type} -> ({x : _} -> Elem x xs -> b x) -> b y -> Elem x (y :: xs) -> b x
extend _ x Here = x
extend f _ (There p) = f p

mapWithElem : (xs : Vect n a) -> ({x : a} -> Elem x xs -> b) -> Vect n b
mapWithElem [] _ = []
mapWithElem (x :: xs) f = f Here :: mapWithElem xs (f . There)

map : (f : a -> b) -> Elem x xs -> Elem (f x) (map f xs)
map _ Here = Here
map f (There p) = There (map f p)

instance Uninhabited (Elem x []) where
  uninhabited Here impossible

notElem : Not (x = y) -> Not (Elem x ys) -> Not (Elem x (y :: ys))
notElem notHere _ Here = notHere Refl
notElem _ notThere (There p) = notThere p

decElem : DecEq a => (x : a) -> (xs : Vect n a) -> Dec (Elem x xs)
decElem x [] = No uninhabited
decElem x (y :: ys) with (x =? y)
  decElem x (x :: _) | Yes Refl = Yes Here
  decElem x (_ :: ys) | No notHere =
    case decElem x ys of
      Yes p => Yes (There p)
      No notThere => No (notElem notHere notThere)

