module PVect

import Data.Fin
import Data.Vect

import Util.Ex
import Util.LTE
import Util.Sigma

%default total

namespace PVect
  ||| Predicate Vect - PVect p xs is isomorphic to HVect (map p xs), but often more convenient
  data PVect : (a -> Type) -> Vect n a -> Type where
    Nil : PVect p []
    (::) : p x -> PVect p xs -> PVect p (x :: xs)

  (++) : PVect p as -> PVect p bs -> PVect p (as ++ bs)
  [] ++ ys = ys
  (x :: xs) ++ ys = x :: xs ++ ys

  unzip : (xs : Vect n (Ex p)) -> PVect p (map fst xs)
  unzip [] = []
  unzip (E x :: xs) = x :: unzip xs

  mapToVect : {ps : Vect n a} -> {p : a -> Type} -> (f : {x : a} -> p x -> q) -> PVect p ps -> Vect n q
  mapToVect {ps = []} f [] = []
  mapToVect {ps = _ :: _} f (x :: xs) = f x :: mapToVect f xs

  mapToPVect : {p : a -> Type} -> (f : (x : a) -> p x) -> (xs : Vect n a) -> PVect p xs
  mapToPVect f [] = []
  mapToPVect f (x :: xs) = f x :: mapToPVect f xs

  zipWithToVect : {ps : Vect n a} -> ({x : a} -> p x -> q x -> c) -> PVect p ps -> PVect q ps -> Vect n c
  zipWithToVect {ps = []} f [] [] = []
  zipWithToVect {ps = _ :: _} f (x :: xs) (y :: ys) = f x y :: zipWithToVect f xs ys

  replicate : {ps : Vect n a} -> ({x : a} -> p x) -> PVect p ps
  replicate {ps = []} x = []
  replicate {ps = _ :: _} x = x :: replicate x

  map : (f : a -> b) -> ({x : a} -> p x -> q (f x)) -> PVect p ps -> PVect q (map f ps)
  map {ps = []} f g [] = []
  map {ps = _ :: _} f g (x :: xs) = g x :: map f g xs

  mapId : ({x : a} -> p x -> q x) -> PVect p ps -> PVect q ps
  mapId {ps = []} g [] = []
  mapId {ps = _ :: _} g (x :: xs) = g x :: mapId g xs

  index : (i : Fin n) -> PVect p ps -> p (index i ps)
  index {ps = _ :: _} FZ (x :: _) = x
  index {ps = _ :: _} (FS n) (_ :: xs) = index n xs

  indexElem : Elem x ps -> PVect p ps -> p x
  indexElem Here (x :: _) = x
  indexElem (There p) (_ :: xs) = indexElem p xs

  -- it can't really infer m . p
  sequence : Applicative m => {p : a -> Type} -> PVect (m . p) ps -> m (PVect p ps)
  sequence {ps = []} [] = pure []
  sequence {ps = _ :: _} (x :: xs) = [| x :: sequence xs |]

namespace LTE
  raise : PVect (\x => x `LTE` y) xs -> y `LTE` z -> PVect (\x => x `LTE` z) xs
  raise {xs = []} [] _ = []
  raise {xs = _ :: _} (p :: ps) q = lteTrans p q :: raise ps q

  upperBound : (xs : Vect n Nat) -> (y ** PVect (\x => x `LTE` y) xs)
  upperBound [] = (Z ** [])
  upperBound [x] = (x ** [lteRefl])
  upperBound (x :: xs) =
    let (y ** ps) = upperBound xs in
      case decLTE x y of
        Left x_lte_y => (y ** x_lte_y :: ps)
        Right y_lte_x => (x ** lteRefl :: raise ps y_lte_x)
