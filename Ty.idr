module Ty

import Data.Fin
import Data.Vect

import Partial
import PiVect

import Util.Dec
import Util.Union
import Util.Vect

%default total

-- needs to be depth tagged too, to make the assert_totals go away
infixr 2 :->
data Ty
  = Bool
  | Num
  | Tuple (Vect n Ty)
  | Sum (Vect n Ty)
  | (:->) Ty Ty

toType : Ty -> Type
toType Bool = Bool
toType Num = Float
toType (s :-> t) = toType s -> Partial (toType t)
toType (Tuple tys) = PiVect (assert_total toType) tys
toType (Sum tys) = Union (map (assert_total toType) tys)

instance Requires (Tuple ss = Tuple ts) (ss ~=~ ts) where
  because contra Refl = contra Refl

instance Requires (Sum ss = Sum ts) (ss ~=~ ts) where
  because contra Refl = contra Refl

instance Requires (s :-> t = s' :-> t') (s = s') where
  because contra Refl = contra Refl

instance Requires (s :-> t = s' :-> t') (t = t') where
  because contra Refl = contra Refl

instance DecEq Ty where
  decEq Bool Bool = Yes Refl

  decEq Num Num = Yes Refl

  -- this assert is also stupid
  decEq (Tuple ss) (Tuple ts) with (assert_total (ss =? ts))
    decEq (Tuple ss) (Tuple ss) | Yes Refl = Yes Refl
    decEq (Tuple ss) (Tuple ts) | No contra = No (because contra)

  decEq (Sum ss) (Sum ts) with (assert_total (ss =? ts))
    decEq (Sum ss) (Sum ss) | Yes Refl = Yes Refl
    decEq (Sum ss) (Sum ts) | No contra = No (because contra)

  decEq (s :-> t) (s' :-> t') with (s =? s', t =? t')
    decEq (s :-> t) (s :-> t) | (Yes Refl, Yes Refl) = Yes Refl
    decEq (s :-> t) (s' :-> t') | (No contra, _) = No (because contra)
    decEq (s :-> t) (s' :-> t') | (_, No contra) = No (because contra)

  decEq Bool Num = No (\Refl impossible)
  decEq Bool (Tuple xs) = No (\Refl impossible)
  decEq Bool (Sum xs) = No (\Refl impossible)
  decEq Bool (x :-> y) = No (\Refl impossible)

  decEq Num Bool = No (\Refl impossible)
  decEq Num (Tuple xs) = No (\Refl impossible)
  decEq Num (Sum xs) = No (\Refl impossible)
  decEq Num (x :-> y) = No (\Refl impossible)

  decEq (Tuple ts) Num = No (\Refl impossible)
  decEq (Tuple ts) Bool = No (\Refl impossible)
  decEq (Tuple ss) (Sum ts) = No (\Refl impossible)
  decEq (Tuple ts) (x :-> y) = No (\Refl impossible)

  decEq (Sum ts) Num = No (\Refl impossible)
  decEq (Sum ts) Bool = No (\Refl impossible)
  decEq (Sum ss) (Tuple ts) = No (\Refl impossible)
  decEq (Sum ts) (x :-> y) = No (\Refl impossible)

  decEq (x :-> y) Num = No (\Refl impossible)
  decEq (x :-> y) (Tuple xs) = No (\Refl impossible)
  decEq (x :-> y) (Sum xs) = No (\Refl impossible)
  decEq (x :-> y) Bool = No (\Refl impossible)
