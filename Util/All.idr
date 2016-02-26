module Util.All

import Data.Fin
import Data.HVect
import Data.Vect
import Data.Vect.Quantifiers

import Util.Elem
import Util.Eq
import Util.Ex
import Util.LTE
import Util.Sigma
import Util.Vect

%default total

toHVect : All p as -> HVect (map p as)
toHVect [] = []
toHVect (x :: xs) = x :: toHVect xs

fromHVect : HVect (map p as) -> All p as
fromHVect {as = []} [] = []
fromHVect {as = _ :: _} (x :: xs) = x :: fromHVect xs

toHVectId : All Basics.id as -> HVect as
toHVectId = replace mapIdNeutral . toHVect

(++) : All p as -> All p bs -> All p (as ++ bs)
[] ++ ys = ys
(x :: xs) ++ ys = x :: xs ++ ys

unzipEx : (xs : Vect n (Ex p)) -> All p (map Ex.fst xs)
unzipEx [] = []
unzipEx (E x :: xs) = x :: unzipEx xs

mapToVect : {ps : Vect n a} -> {p : a -> Type} -> (f : {x : a} -> p x -> q) -> All p ps -> Vect n q
mapToVect {ps = []} f [] = []
mapToVect {ps = _ :: _} f (x :: xs) = f x :: mapToVect f xs

mapToAll : {p : b -> Type} -> {f : a -> b} -> ((x : a) -> p (f x)) -> (xs : Vect n a) -> All p (map f xs)
mapToAll f [] = []
mapToAll f (x :: xs) = f x :: mapToAll f xs

mapToAll' : {p : a -> Type} -> ((x : a) -> p x) -> (xs : Vect n a) -> All p xs
mapToAll' f [] = []
mapToAll' f (x :: xs) = f x :: mapToAll' f xs

zipWithToVect : {ps : Vect n a} -> ({x : a} -> p x -> q x -> c) -> All p ps -> All q ps -> Vect n c
zipWithToVect {ps = []} f [] [] = []
zipWithToVect {ps = _ :: _} f (x :: xs) (y :: ys) = f x y :: zipWithToVect f xs ys

replicate : {ps : Vect n a} -> ({x : a} -> p x) -> All p ps
replicate {ps = []} x = []
replicate {ps = _ :: _} x = x :: replicate x

map : (f : a -> b) -> ({x : a} -> p x -> q (f x)) -> All p ps -> All q (map f ps)
map {ps = []} f g [] = []
map {ps = _ :: _} f g (x :: xs) = g x :: map f g xs

map' : ({x : a} -> p x -> q x) -> All p ps -> All q ps
map' {ps = []} g [] = []
map' {ps = _ :: _} g (x :: xs) = g x :: map' g xs

cong : ((x : _) -> p x = q x) -> All p xs -> All q xs
cong eq = map' (replace' (eq _))

index : (i : Fin n) -> All p ps -> p (index i ps)
index {ps = _ :: _} FZ (x :: _) = x
index {ps = _ :: _} (FS n) (_ :: xs) = index n xs

indexElem : Elem x ps -> All p ps -> p x
indexElem Here (x :: _) = x
indexElem (There p) (_ :: xs) = indexElem p xs

sequence : Applicative m => {p : a -> Type} -> All (m . p) ps -> m (All p ps)
sequence {ps = []} [] = pure []
sequence {ps = _ :: _} (x :: xs) = [| x :: sequence xs |]

sequenceMap' : Applicative m => ({x : a} -> p x -> m (q x)) -> All p xs -> m (All q xs)
sequenceMap' f = sequence . map' f
