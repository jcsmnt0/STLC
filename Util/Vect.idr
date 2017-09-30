module Util.Vect

import Data.Vect

import Util.Dec
import Util.Ex

%default total
%access export

toVect : (xs : List a) -> Vect (length xs) a
toVect [] = []
toVect (x :: xs) = x :: toVect xs

mapIdNeutral : {xs : Vect n a} -> map Basics.id xs = xs
mapIdNeutral {xs = []} = Refl
mapIdNeutral {xs = _ :: _} = cong mapIdNeutral

mapDistributesOverAppend : {xs : Vect m a} -> map f (xs ++ ys) = map f xs ++ map f ys
mapDistributesOverAppend {xs = []} = Refl
mapDistributesOverAppend {xs = _ :: _} = cong mapDistributesOverAppend

indexDistributesOverMap : {xs : Vect n a} -> index i (map f xs) = f (index i xs)
indexDistributesOverMap {xs = _ :: _} {i = FZ} = Refl
indexDistributesOverMap {xs = _ :: _} {i = FS _} = indexDistributesOverMap

mapFstZipLemma : map Basics.fst (Vect.zip xs ys) = xs
mapFstZipLemma {xs = []} {ys = []} = Refl
mapFstZipLemma {xs = _ :: _} {ys = _ :: _} = cong mapFstZipLemma

mapSndZipLemma : map Basics.snd (Vect.zip xs ys) = ys
mapSndZipLemma {xs = []} {ys = []} = Refl
mapSndZipLemma {xs = _ :: _} {ys = _ :: _} = cong mapSndZipLemma

Uninhabited (the (Vect _ a) Nil ~=~ the (Vect _ a) (x :: xs)) where
  uninhabited Refl impossible

Uninhabited (the (Vect _ a) (x :: xs) ~=~ the (Vect _ a) Nil) where
  uninhabited Refl impossible

vectInjective1 : {x, y : a} -> {xs : Vect n a} -> {ys : Vect m a} ->
                 x :: xs = y :: ys -> x = y
vectInjective1 Refl = Refl

vectInjective2 : {x, y : a} -> {xs : Vect n a} -> {ys : Vect m a} ->
                 x :: xs = y :: ys -> xs ~=~ ys
vectInjective2 Refl = Refl

consEq : {x, y : a} -> {xs : Vect m a} -> {ys : Vect n a} ->
         x = y -> xs = ys -> x :: xs = y :: ys
consEq Refl Refl = Refl

namespace Vect
  (=?) : DecEq a => (xs : Vect m a) -> (ys : Vect n a) -> Dec (xs = ys)
  [] =? [] = Yes Refl
  (_ :: _) =? [] = No uninhabited
  [] =? (_ :: _) = No uninhabited
  (x :: xs) =? (y :: ys) with (decEq x y)
    (x :: xs) =? (x :: ys) | Yes Refl with (xs =? ys)
      (x :: xs) =? (x :: ys) | Yes Refl | Yes prf = Yes (consEq Refl prf) 
      (x :: xs) =? (x :: ys) | Yes Refl | No neq = No (neq . vectInjective2)
    (x :: xs) =? (y :: ys) | No neq = No (neq . vectInjective1)

