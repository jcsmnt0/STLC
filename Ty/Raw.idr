module Ty.Raw

import Data.Vect

import Util.Dec
import Util.Vect

%default total

infixr 10 :->

data Ty
  = NUM
  | (:->) Ty Ty
  | Tuple (Vect n Ty)
  | Sum (Vect n Ty)

VOID : Ty
VOID = Sum []

UNIT : Ty
UNIT = Tuple []

BOOL : Ty
BOOL = Sum [UNIT, UNIT]

LAZY : Ty -> Ty
LAZY a = UNIT :-> a

Requires (Tuple ss = Tuple ts) (ss ~=~ ts) where
  because contra Refl = contra Refl

Requires (Sum ss = Sum ts) (ss ~=~ ts) where
  because contra Refl = contra Refl

Requires (s :-> t = s' :-> t') (s = s') where
  because contra Refl = contra Refl

Requires (s :-> t = s' :-> t') (t = t') where
  because contra Refl = contra Refl

DecEq Ty where
  decEq NUM NUM = Yes Refl

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

  decEq NUM (Tuple xs) = No (\Refl impossible)
  decEq NUM (Sum xs) = No (\Refl impossible)
  decEq NUM (x :-> y) = No (\Refl impossible)

  decEq (Tuple ts) NUM = No (\Refl impossible)
  decEq (Tuple ss) (Sum ts) = No (\Refl impossible)
  decEq (Tuple ts) (x :-> y) = No (\Refl impossible)

  decEq (Sum ts) NUM = No (\Refl impossible)
  decEq (Sum ss) (Tuple ts) = No (\Refl impossible)
  decEq (Sum ts) (x :-> y) = No (\Refl impossible)

  decEq (x :-> y) NUM = No (\Refl impossible)
  decEq (x :-> y) (Tuple xs) = No (\Refl impossible)
  decEq (x :-> y) (Sum xs) = No (\Refl impossible)
