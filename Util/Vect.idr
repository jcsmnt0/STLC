module Util.Vect

import Data.Vect

import Util.Dec
import Util.Ex

%default total

toVect : List a -> Ex (flip Vect a)
toVect [] = E []
toVect (x :: xs) = let E xs' = toVect xs in E (x :: xs')

instance Uninhabited (Vect.Nil ~=~ x :: the (Vect m a) xs) where
  uninhabited Refl impossible

instance Uninhabited (x :: the (Vect m a) xs ~=~ Vect.Nil) where
  uninhabited Refl impossible

instance Requires (x :: the (Vect m a) xs = y :: the (Vect n a) ys) (x = y) where
  because contra Refl = contra Refl

instance Requires (x :: the (Vect m a) xs = y :: the (Vect n a) ys) (xs ~=~ ys) where
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
