module Ty

import Data.Fin
import Data.HVect
import Data.Vect
import Data.Vect.Quantifiers

import Partial
import Syntax

import Util.All
import Util.Dec
import Util.Elem
import Util.Eq
import Util.Fin
import Util.Union
import Util.Vect

%default total

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

%name Ty a, b, c

fromSynTy : SynTy -> Ty.Ty l
fromSynTy NUM = NUM
fromSynTy (a :-> b) = fromSynTy a :-> fromSynTy b
fromSynTy (Tuple as) = Tuple $ map (assert_total fromSynTy) as
fromSynTy (Sum as) = Sum $ map (assert_total fromSynTy) as

namespace Ty
  -- this is (roughly) automatically implicit because it's a special name
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

  mutual
    weakenApplyCancel : a = weaken a :@ b
    weakenApplyCancel {a = C a} = Refl
    weakenApplyCancel {a = Var FZ} = Refl
    weakenApplyCancel {a = Var (FS _)} = Refl
    weakenApplyCancel {a = a :-> b} = cong2 {f = \a', b' => a' :-> b'} weakenApplyCancel weakenApplyCancel
    weakenApplyCancel {a = Tuple as} {b = b} = cong $ assert_total $ weakenApplyCancelVect as b
    weakenApplyCancel {a = Sum as} {b = b} = cong $ assert_total $ weakenApplyCancelVect as b

    weakenApplyCancelVect : (as : Ty.Ctx _ _) -> (b : _) -> as = map (:@ b) (map Ty.weaken as)
    weakenApplyCancelVect [] b = Refl
    weakenApplyCancelVect (a :: as) b = cong2 weakenApplyCancel (weakenApplyCancelVect as b)

namespace Ctx
  weaken : Ctx l n -> Ctx (S l) n
  weaken = map weaken

Val : Vect l Type -> Ty l -> Type
Val e (C a) = a
Val e (Var i) = index i e
Val e (a :-> b) = Val e a -> Partial (Val e b)
Val e (Tuple as) = HVect (map (assert_total $ Val e) as)
Val e (Sum as) = Union (map (assert_total $ Val e) as)

normalize : Vect l Type -> Ty l -> Ty l
normalize e = C . Val e

namespace Val
  mutual
    betaValLemma : Val e (a :@ b) = Val (Val e b :: e) a
    betaValLemma {a = C a} = Refl
    betaValLemma {a = Var FZ} = Refl
    betaValLemma {a = Var (FS _)} = Refl
    betaValLemma {a = a :-> b} = cong2 {f = \a', b' => a' -> Partial b'} betaValLemma betaValLemma
    betaValLemma {a = Tuple as} = cong $ assert_total betaValTupleLemma
    betaValLemma {a = Sum as} = cong $ assert_total betaValSumLemma

    betaValTupleLemma : {as : Ty.Ctx _ _} -> map (Val e) (map (:@ b) as) = map (Val (Val e b :: e)) as
    betaValTupleLemma {as = []} = Refl
    betaValTupleLemma {as = a :: as} = cong2 betaValLemma betaValTupleLemma

    betaValSumLemma : {as : Ty.Ctx _ _} -> map (Val e) (map (:@ b) as) = map (Val (Val e b :: e)) as
    betaValSumLemma {as = []} = Refl
    betaValSumLemma {as = a :: as} = cong2 betaValLemma betaValSumLemma

  -- reduction at the type level, not term level
  betaReduceTy : Val e (a :@ b) -> Val (Val e b :: e) a
  betaReduceTy = replace' betaValLemma

  betaExpandTy : Val (Val e b :: e) a -> Val e (a :@ b)
  betaExpandTy = replace' (sym betaValLemma)

  weakenValLemma : Val e a = Val (b :: e) (Ty.weaken a)
  weakenValLemma {b = b} = Eq.trans (cong weakenApplyCancel) (betaValLemma {b = C b})

  weaken : Val e a -> Val (b :: e) (weaken a)
  weaken = replace' weakenValLemma

  strengthen : Val (b :: e) (weaken a) -> Val e a
  strengthen = replace' (sym weakenValLemma)

Env : Vect l Type -> Ctx l n -> Type
Env e = All (Val e)

namespace Env
  weaken : {e : Vect l Type} -> {g : Ctx l n} -> Env e g -> Env (a :: e) (Ctx.weaken g)
  weaken = map Ty.weaken Val.weaken
