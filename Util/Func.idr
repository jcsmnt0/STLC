module Util.Func

import Data.HVect

%default total

Func : Vect n Type -> Type -> Type
Func [] b = b
Func (a :: as) b = a -> Func as b

apply : Func as b -> HVect as -> b
apply x [] = x
apply f (x :: xs) = apply (f x) xs

compose : (b -> c) -> Func as b -> Func as c
compose {as = []} g x = g x
compose {as = _ :: _} g f = \x => compose g (f x)
