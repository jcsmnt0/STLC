module PiVect

import Data.Fin
import Data.Vect

import Util.Ex
import Util.LTE
import Util.Sigma

%default total

namespace PiVect
  data PiVect : (a -> Type) -> Vect n a -> Type where
    Nil : PiVect p []
    (::) : p x -> PiVect p xs -> PiVect p (x :: xs)

  (++) : PiVect p as -> PiVect p bs -> PiVect p (as ++ bs)
  [] ++ ys = ys
  (x :: xs) ++ ys = x :: xs ++ ys

  unzip : (xs : Vect n (Ex p)) -> PiVect p (map fst xs)
  unzip [] = []
  unzip (E x :: xs) = x :: unzip xs

  mapToVect : {ps : Vect n a} -> {p : a -> Type} -> (f : {x : a} -> p x -> q) -> PiVect p ps -> Vect n q
  mapToVect {ps = []} f [] = []
  mapToVect {ps = _ :: _} f (x :: xs) = f x :: mapToVect f xs

  mapToPiVect : {p : a -> Type} -> (f : (x : a) -> p x) -> (xs : Vect n a) -> PiVect p xs
  mapToPiVect f [] = []
  mapToPiVect f (x :: xs) = f x :: mapToPiVect f xs

  zipWithToVect : {ps : Vect n a} -> ({x : a} -> p x -> q x -> c) -> PiVect p ps -> PiVect q ps -> Vect n c
  zipWithToVect {ps = []} f [] [] = []
  zipWithToVect {ps = _ :: _} f (x :: xs) (y :: ys) = f x y :: zipWithToVect f xs ys

  map : (f : a -> b) -> ({x : a} -> p x -> q (f x)) -> PiVect p ps -> PiVect q (map f ps)
  map {ps = []} f g [] = []
  map {ps = _ :: _} f g (x :: xs) = g x :: map f g xs

  mapId : ({x : a} -> p x -> q x) -> PiVect p ps -> PiVect q ps
  mapId {ps = []} g [] = []
  mapId {ps = _ :: _} g (x :: xs) = g x :: mapId g xs

  index : (i : Fin n) -> PiVect p ps -> p (index i ps)
  index {ps = _ :: _} FZ (x :: _) = x
  index {ps = _ :: _} (FS n) (_ :: xs) = index n xs

  indexElem : Elem x ps -> PiVect p ps -> p x
  indexElem Here (x :: _) = x
  indexElem (There p) (_ :: xs) = indexElem p xs

  -- it can't really infer m . p
  sequence : Applicative m => {p : a -> Type} -> PiVect (m . p) ps -> m (PiVect p ps)
  sequence {ps = []} [] = pure []
  sequence {ps = _ :: _} (x :: xs) = [| x :: sequence xs |]

namespace LTE
  raise : PiVect (\x => x `LTE` y) xs -> y `LTE` z -> PiVect (\x => x `LTE` z) xs
  raise {xs = []} [] _ = []
  raise {xs = _ :: _} (p :: ps) q = lteTrans p q :: raise ps q

  upperBound : (xs : Vect n Nat) -> (y ** PiVect (\x => x `LTE` y) xs)
  upperBound [] = (Z ** [])
  upperBound [x] = (x ** [lteRefl])
  upperBound (x :: xs) =
    let (y ** ps) = upperBound xs in
      case decLTE x y of
        Left x_lte_y => (y ** x_lte_y :: ps)
        Right y_lte_x => (x ** lteRefl :: raise ps y_lte_x)
