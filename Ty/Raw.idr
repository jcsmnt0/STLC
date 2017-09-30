module Ty.Raw

import Data.Vect

import Util.Dec
import Util.Vect

%default total
%access public export

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

private
tupleEqThenVectEq : {ss : Vect n Ty} -> {ts : Vect m Ty} ->
                    (Tuple ss = Tuple ts) -> (ss ~=~ ts)
tupleEqThenVectEq Refl = Refl

private
sumEqThenVectEq : {ss : Vect n Ty} -> {ts : Vect m Ty} ->
                  (Sum ss = Sum ts) -> (ss ~=~ ts)
sumEqThenVectEq Refl = Refl

private
arrayEqThenLeftEq : {s, s', t, t' : Ty} -> (s :-> t = s' :-> t') -> s = s'
arrayEqThenLeftEq Refl = Refl

private
arrayEqThenRightEq : {s, s', t, t' : Ty} -> (s :-> t = s' :-> t') -> t = t'
arrayEqThenRightEq Refl = Refl

DecEq Ty where
  decEq NUM NUM = Yes Refl

  decEq (s :-> t) (s' :-> t') with (s =? s', t =? t')
    decEq (s :-> t) (s :-> t) | (Yes Refl, Yes Refl) = Yes Refl
    decEq (s :-> t) (s' :-> t') | (No contra, _) = No (contra . arrayEqThenLeftEq)
    decEq (s :-> t) (s' :-> t') | (_, No contra) = No (contra . arrayEqThenRightEq)

  decEq (Tuple ss) (Tuple ts) with (assert_total (ss =? ts))
    decEq (Tuple ss) (Tuple ts) | Yes prf = Yes (rewrite prf in Refl)
    decEq (Tuple ss) (Tuple ts) | (No contra) = No (contra . tupleEqThenVectEq)

  decEq (Sum ss) (Sum ts) with (assert_total (ss =? ts))
    decEq (Sum ss) (Sum ts) | Yes prf = Yes (rewrite prf in Refl)
    decEq (Sum ss) (Sum ts) | (No contra) = No (contra . sumEqThenVectEq)

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

