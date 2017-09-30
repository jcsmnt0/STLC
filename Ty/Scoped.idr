module Ty.Scoped

import Data.Fin
import Data.Vect

import Ty.Raw

import Util.Eq

%default total
%access public export

infixr 10 :->
infixr 9 :@

data Ty : Nat -> Type where
  C : Type -> Ty l
  Var : Fin l -> Ty l
  (:->) : Ty l -> Ty l -> Ty l
  Tuple : Vect n (Ty l) -> Ty l
  Sum : Vect n (Ty l) -> Ty l

VOID : Ty l
VOID = Sum []

UNIT : Ty l
UNIT = Tuple []

BOOL : Ty l
BOOL = Sum [UNIT, UNIT]

NUM : Ty l
NUM = C Nat

LAZY : Ty l -> Ty l
LAZY a = UNIT :-> a

fromRawTy : Raw.Ty -> Scoped.Ty l
fromRawTy NUM = NUM
fromRawTy (a :-> b) = fromRawTy a :-> fromRawTy b
fromRawTy (Tuple as) = Tuple $ map (assert_total fromRawTy) as
fromRawTy (Sum as) = Sum $ map (assert_total fromRawTy) as

-- this is (roughly) automatically implicit because it's a special name
private
fromInteger : (x : Integer) -> {default ItIsJust p : IsJust (integerToFin x l)} -> Ty l
fromInteger x {p = p} = Var $ fromInteger {prf = p} x

sub : (Fin l -> Ty d') -> Ty l -> Ty d'
sub f (C a) = C a
sub f (Var i) = f i
sub f (a :-> b) = sub f a :-> sub f b
sub f (Tuple as) = Tuple $ map (assert_total $ sub f) as
sub f (Sum as) = Sum $ map (assert_total $ sub f) as

weakenN : (n : Nat) -> Ty l -> Ty (n + l)
weakenN n = sub (Var . shift n)

weaken : Ty l -> Ty (S l)
weaken = weakenN 1

betaSub : Ty l -> Fin (S l) -> Ty l
betaSub a FZ = a
betaSub a (FS i) = Var i

(:@) : Ty (S l) -> Ty l -> Ty l
(:@) a b = sub (betaSub b) a

Ctx : Nat -> Nat -> Type
Ctx l n = Vect n (Ty l)

namespace Ctx
  weaken : Ctx l n -> Ctx (S l) n
  weaken = map weaken

mutual
  export
  weakenApplyCancel : a = weaken a :@ b
  weakenApplyCancel {a = C a} = Refl
  weakenApplyCancel {a = Var FZ} = Refl
  weakenApplyCancel {a = Var (FS _)} = Refl
  weakenApplyCancel {a = a :-> b} = cong2 {f = \a', b' => a' :-> b'} weakenApplyCancel weakenApplyCancel
  weakenApplyCancel {a = Tuple as} {b = b} = cong $ assert_total $ weakenApplyCancelVect as b
  weakenApplyCancel {a = Sum as} {b = b} = cong $ assert_total $ weakenApplyCancelVect as b

  export
  weakenApplyCancelVect : (as : Ctx l n) -> (b : Ty l) -> as = map (:@ b) (map Scoped.weaken as)
  weakenApplyCancelVect [] b = Refl
  weakenApplyCancelVect (a :: as) b = cong2 weakenApplyCancel (weakenApplyCancelVect as b)
