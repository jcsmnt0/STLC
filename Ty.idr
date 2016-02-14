module Ty

import Data.Fin
import Data.Vect
import Data.Vect.Quantifiers

import Partial

import Util.Dec
import Util.Union
import Util.Vect

%default total

-- it seems like it's possible to tag Tys with depth like Terms and other things and avoid the assert_total calls,
-- but it gets to be a really big hassle.
infixr 2 :->
data Ty
  = Bool
  | Num
  | Tuple (Vect n Ty)
  | Sum (Vect n Ty)
  | (:->) Ty Ty

Val : Ty -> Type
Val Bool = Bool
Val Num = Double
Val (s :-> t) = Val s -> Partial (Val t)
Val (Tuple tys) = All (assert_total Val) tys
Val (Sum tys) = Union (map (assert_total Val) tys)

Requires (Tuple ss = Tuple ts) (ss ~=~ ts) where
  because contra Refl = contra Refl

Requires (Sum ss = Sum ts) (ss ~=~ ts) where
  because contra Refl = contra Refl

Requires (s :-> t = s' :-> t') (s = s') where
  because contra Refl = contra Refl

Requires (s :-> t = s' :-> t') (t = t') where
  because contra Refl = contra Refl

DecEq Ty where
  decEq Bool Bool = Yes Refl

  decEq Num Num = Yes Refl

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
