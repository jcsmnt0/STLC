module PiVect

import Data.Fin
import Data.Vect

import Util.Ex
import Util.LTE
import Util.Sigma

%default total

Func : Vect n Type -> Type -> Type
Func [] b = b
Func (a :: as) b = a -> Func as b

namespace PiVect
  data PiVect : (a -> Type) -> Vect n a -> Type where
    Nil : PiVect p []
    (::) : p x -> PiVect p xs -> PiVect p (x :: xs)

  fromVect : Vect n a -> PiVect (const a) (replicate n ())
  fromVect [] = []
  fromVect (x :: xs) = x :: fromVect xs

  fromSigmas : (ys : Vect n (x : a ** b x)) -> PiVect b (map Dependent.fst ys)
  fromSigmas [] = []
  fromSigmas (x :: xs) = (::) {x = Dependent.fst x} (Dependent.snd x) (fromSigmas xs)

  unzip :
    {p : Pair a b -> Type} ->
    {xs : Vect n a} ->
    PiVect (\x => (y : b ** p (x, y))) xs ->
    (ys : Vect n b ** PiVect p (zip xs ys))
  unzip {xs = []} [] = ([] ** [])
  unzip {xs = _ :: _} ((y ** p) :: prs) = let (ys ** ps) = unzip prs in (y :: ys ** p :: ps)

  unzipEx : (xs : Vect n (Ex p)) -> PiVect p (map fst xs)
  unzipEx [] = []
  unzipEx (E x :: xs) = x :: unzipEx xs

  unzipToPiVect : Vect n (x : a ** b x) -> (xs : Vect n a ** PiVect b xs)
  unzipToPiVect [] = ([] ** [])
  unzipToPiVect ((x ** y) :: prs) = let (xs ** ys) = unzipToPiVect prs in (x :: xs ** y :: ys)

  mapToVect : {ps : Vect n a} -> {p : a -> Type} -> (f : {x : a} -> p x -> q) -> PiVect p ps -> Vect n q
  mapToVect {ps = []} f [] = []
  mapToVect {ps = _ :: _} f (x :: xs) = f x :: mapToVect f xs

  zipWithToVect :
    {ps : Vect n a} ->
    ({x : a} -> p x -> q x -> c) ->
    PiVect p ps ->
    PiVect q ps ->
    Vect n c
  zipWithToVect {ps = []} f [] [] = []
  zipWithToVect {ps = _ :: _} f (x :: xs) (y :: ys) = f x y :: zipWithToVect f xs ys

  mapToPiVect : {p : a -> Type} -> (f : (x : a) -> p x) -> (ps : Vect n a) -> PiVect p ps
  mapToPiVect f [] = []
  mapToPiVect f (x :: xs) = f x :: mapToPiVect f xs

  map :
    (f : a -> b) ->
    ({x : a} -> p x -> q (f x)) ->
    PiVect p ps ->
    PiVect q (map f ps)
  map {ps = []} f g [] = []
  map {ps = _ :: _} f g (x :: xs) = g x :: map f g xs

  mapId :
    ({x : a} -> p x -> q x) ->
    PiVect p ps ->
    PiVect q ps
  mapId {ps = []} g [] = []
  mapId {ps = _ :: _} g (x :: xs) = g x :: mapId g xs

  index : (i : Fin n) -> PiVect p ps -> p (index i ps)
  index {ps = _ :: _} FZ (x :: _) = x
  index {ps = _ :: _} (FS n) (_ :: xs) = index n xs

  indexElem : Elem x ps -> PiVect p ps -> p x
  indexElem Here (x :: _) = x
  indexElem (There p) (_ :: xs) = indexElem p xs

  -- it can't really infer m . p - a DSL for those predicates would be useful
  sequence : Monad m => {p : a -> Type} -> PiVect (m . p) ps -> m (PiVect p ps)
  sequence {ps = []} [] = return []
  sequence {ps = _ :: _} (x :: xs) = do
    x' <- x
    xs' <- PiVect.sequence xs
    return (x' :: xs')

namespace Vect
  map :
    (f : (x : a) -> p x) ->
    (ps : Vect n a) ->
    PiVect p ps
  map f [] = []
  map f (x :: xs) = f x :: map f xs

  zipWithR :
    {ys : Vect n b} ->
    (f : {y : b} -> a -> q y -> c) ->
    Vect n a ->
    PiVect q ys ->
    Vect n c
  zipWithR {ys = []} f [] [] = []
  zipWithR {ys = _ :: _} f (x :: xs) (y :: ys) = f x y :: zipWithR f xs ys

namespace Elem
  piMapWithElem : (xs : Vect n a) -> ({x : a} -> Elem x xs -> b x) -> PiVect b xs
  piMapWithElem [] _ = []
  piMapWithElem (x :: xs) f = f Here :: piMapWithElem xs (f . There)

namespace LTE
  -- this should be doable with generic PiVect functions
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
