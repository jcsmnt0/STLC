module All

import Data.Fin
import Data.Vect
import Data.Vect.Quantifiers

import Util.Ex
import Util.LTE
import Util.Sigma

%default total

namespace All
  (++) : All p as -> All p bs -> All p (as ++ bs)
  [] ++ ys = ys
  (x :: xs) ++ ys = x :: xs ++ ys

  -- "map fst xs" causes a problem - log as a bug?
  unzip : (xs : Vect n (Ex p)) -> All p (map (\x => fst x) xs)
  unzip [] = []
  unzip (E x :: xs) = x :: unzip xs

  mapToVect : {ps : Vect n a} -> {p : a -> Type} -> (f : {x : a} -> p x -> q) -> All p ps -> Vect n q
  mapToVect {ps = []} f [] = []
  mapToVect {ps = _ :: _} f (x :: xs) = f x :: mapToVect f xs

  mapToAll : {p : a -> Type} -> (f : (x : a) -> p x) -> (xs : Vect n a) -> All p xs
  mapToAll f [] = []
  mapToAll f (x :: xs) = f x :: mapToAll f xs

  zipWithToVect : {ps : Vect n a} -> ({x : a} -> p x -> q x -> c) -> All p ps -> All q ps -> Vect n c
  zipWithToVect {ps = []} f [] [] = []
  zipWithToVect {ps = _ :: _} f (x :: xs) (y :: ys) = f x y :: zipWithToVect f xs ys

  replicate : {ps : Vect n a} -> ({x : a} -> p x) -> All p ps
  replicate {ps = []} x = []
  replicate {ps = _ :: _} x = x :: replicate x

  map : (f : a -> b) -> ({x : a} -> p x -> q (f x)) -> All p ps -> All q (map f ps)
  map {ps = []} f g [] = []
  map {ps = _ :: _} f g (x :: xs) = g x :: map f g xs

  mapId : ({x : a} -> p x -> q x) -> All p ps -> All q ps
  mapId {ps = []} g [] = []
  mapId {ps = _ :: _} g (x :: xs) = g x :: mapId g xs

  index : (i : Fin n) -> All p ps -> p (index i ps)
  index {ps = _ :: _} FZ (x :: _) = x
  index {ps = _ :: _} (FS n) (_ :: xs) = index n xs

  indexElem : Elem x ps -> All p ps -> p x
  indexElem Here (x :: _) = x
  indexElem (There p) (_ :: xs) = indexElem p xs

  -- it can't really infer m . p
  sequence : Applicative m => {p : a -> Type} -> All (m . p) ps -> m (All p ps)
  sequence {ps = []} [] = pure []
  sequence {ps = _ :: _} (x :: xs) = [| x :: sequence xs |]

namespace LTE
  raise : All (\x => x `LTE` y) xs -> y `LTE` z -> All (\x => x `LTE` z) xs
  raise {xs = []} [] _ = []
  raise {xs = _ :: _} (p :: ps) q = lteTrans p q :: raise ps q

  upperBound : (xs : Vect n Nat) -> (y ** All (\x => x `LTE` y) xs)
  upperBound [] = (Z ** [])
  upperBound [x] = (x ** [lteRefl])
  upperBound (x :: xs) =
    let (y ** ps) = upperBound xs in
      case decLTE x y of
        Left x_lte_y => (y ** x_lte_y :: ps)
        Right y_lte_x => (x ** lteRefl :: raise ps y_lte_x)
