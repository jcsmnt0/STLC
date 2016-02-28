module Ty.Val

import Data.HVect
import Data.Vect
import Data.Vect.Quantifiers

import Ty.Raw
import Ty.Scoped

import Util.All
import Util.Eq
import Util.Partial
import Util.Union

%default total

Val : Vect l Type -> Ty l -> Type
Val e (C a) = a
Val e (Var i) = index i e
Val e (a :-> b) = Val e a -> Partial (Val e b)
Val e (Tuple as) = HVect (map (assert_total $ Val e) as)
Val e (Sum as) = Union (map (assert_total $ Val e) as)

SynVal : Vect n Type -> Raw.Ty -> Type
SynVal e = Val e . fromRawTy

normalize : Vect l Type -> Ty l -> Ty l
normalize e = C . Val e

mutual
  betaValLemma : Val e (a :@ b) = Val (Val e b :: e) a
  betaValLemma {a = C a} = Refl
  betaValLemma {a = Var FZ} = Refl
  betaValLemma {a = Var (FS _)} = Refl
  betaValLemma {a = a :-> b} = cong2 {f = \a', b' => a' -> Partial b'} betaValLemma betaValLemma
  betaValLemma {a = Tuple as} = cong $ assert_total betaValTupleLemma
  betaValLemma {a = Sum as} = cong $ assert_total betaValSumLemma

  betaValTupleLemma : {as : Ctx _ _} -> map (Val e) (map (:@ b) as) = map (Val (Val e b :: e)) as
  betaValTupleLemma {as = []} = Refl
  betaValTupleLemma {as = a :: as} = cong2 betaValLemma betaValTupleLemma

  betaValSumLemma : {as : Ctx _ _} -> map (Val e) (map (:@ b) as) = map (Val (Val e b :: e)) as
  betaValSumLemma {as = []} = Refl
  betaValSumLemma {as = a :: as} = cong2 betaValLemma betaValSumLemma

betaReduceTy : Val e (a :@ b) -> Val (Val e b :: e) a
betaReduceTy = replace' betaValLemma

betaExpandTy : Val (Val e b :: e) a -> Val e (a :@ b)
betaExpandTy = replace' (sym betaValLemma)

weakenValLemma : Val e a = Val (b :: e) (weaken a)
weakenValLemma {b = b} = Eq.trans (cong weakenApplyCancel) (betaValLemma {b = C b})

weaken : Val e a -> Val (b :: e) (weaken a)
weaken = replace' weakenValLemma

strengthen : Val (b :: e) (weaken a) -> Val e a
strengthen = replace' (sym weakenValLemma)

Env : Vect l Type -> Ctx l n -> Type
Env e = All (Val e)

namespace Env
  weaken : {e : Vect l Type} -> {g : Ctx l n} -> Env e g -> Env (a :: e) (weaken g)
  weaken = map weaken Val.weaken
