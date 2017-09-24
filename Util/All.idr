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

export
toHVect : All p as -> HVect (map p as)
toHVect [] = []
toHVect (x :: xs) = x :: toHVect xs

export
fromHVect : HVect (map p as) -> All p as
fromHVect {as = []} [] = []
fromHVect {as = _ :: _} (x :: xs) = x :: fromHVect xs

toHVectId : All Basics.id as -> HVect as
toHVectId = replace mapIdNeutral . toHVect

export
(++) : All p as -> All p bs -> All p (as ++ bs)
[] ++ ys = ys
(x :: xs) ++ ys = x :: xs ++ ys

export
unzipEx : (as : Vect n (Ex p)) -> All p (map Ex.fst as)
unzipEx [] = []
unzipEx (x :: xs) = snd x :: unzipEx xs

mapToVect : {as : Vect n a} -> {p : a -> Type} -> (f : {x : a} -> p x -> q) -> All p as -> Vect n q
mapToVect {as = []} f [] = []
mapToVect {as = _ :: _} f (x :: xs) = f x :: mapToVect f xs

mapToAll : {p : b -> Type} -> {f : a -> b} -> ((x : a) -> p (f x)) -> (as : Vect n a) -> All p (map f as)
mapToAll f [] = []
mapToAll f (x :: xs) = f x :: mapToAll f xs

mapToAll' : {p : a -> Type} -> ((x : a) -> p x) -> (as : Vect n a) -> All p as
mapToAll' f [] = []
mapToAll' f (x :: xs) = f x :: mapToAll' f xs

export
zipWithToVect : {as : Vect n a} -> ({x : a} -> p x -> q x -> c) -> All p as -> All q as -> Vect n c
zipWithToVect {as = []} f [] [] = []
zipWithToVect {as = _ :: _} f (x :: xs) (y :: ys) = f x y :: zipWithToVect f xs ys

replicate : {as : Vect n a} -> ({x : a} -> p x) -> All p as
replicate {as = []} x = []
replicate {as = _ :: _} x = x :: replicate x

export
map : (f : a -> b) -> ({x : a} -> p x -> q (f x)) -> All p as -> All q (map f as)
map {as = []} f g [] = []
map {as = _ :: _} f g (x :: xs) = g x :: map f g xs

export
map' : ({x : a} -> p x -> q x) -> All p as -> All q as
map' {as = []} g [] = []
map' {as = _ :: _} g (x :: xs) = g x :: map' g xs

cong : ((x : _) -> p x = q x) -> All p as -> All q as
cong eq = map' (replace' (eq _))

export
index : (i : Fin n) -> All p as -> p (index i as)
index {as = _ :: _} FZ (x :: _) = x
index {as = _ :: _} (FS n) (_ :: xs) = index n xs

indexElem : Elem x as -> All p as -> p x
indexElem Here (x :: _) = x
indexElem (There p) (_ :: xs) = indexElem p xs

sequence : Applicative m => {p : a -> Type} -> All (m . p) as -> m (All p as)
sequence {as = []} [] = pure []
sequence {as = _ :: _} (x :: xs) = [| x :: sequence xs |]

export
sequenceMap' : Applicative m => ({x : a} -> p x -> m (q x)) -> All p as -> m (All q as)
sequenceMap' f = sequence . map' f
