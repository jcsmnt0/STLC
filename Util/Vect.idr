module Util.Vect

import Data.Vect

import Util.Dec
import Util.Ex

%default total

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

Uninhabited (Vect.Nil ~=~ x :: the (Vect m a) xs) where
  uninhabited Refl impossible

Uninhabited (x :: the (Vect m a) xs ~=~ Vect.Nil) where
  uninhabited Refl impossible

Requires (x :: the (Vect m a) xs = y :: the (Vect n a) ys) (x = y) where
  because contra Refl = contra Refl

Requires (x :: the (Vect m a) xs = y :: the (Vect n a) ys) (xs ~=~ ys) where
  because contra Refl = contra Refl

namespace Vect
  (=?) : DecEq a => (xs : Vect m a) -> (ys : Vect n a) -> Dec (xs = ys)
  [] =? [] = Yes Refl
  (_ :: _) =? [] = No uninhabited
  [] =? (_ :: _) = No uninhabited
  (x :: xs) =? (y :: ys) = do
    exy <- x =? y
    exsys <- xs =? ys
    Yes (consEq exy exsys)
  where
    consEq : {x, y : a} -> {xs : Vect m a} -> {ys : Vect n a} -> x = y -> xs = ys -> x :: xs = y :: ys
    consEq Refl Refl = Refl
