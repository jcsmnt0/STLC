module Term.Scoped

import Data.Vect

import Ty.Raw

%default total

infixl 9 :$

||| Terms that are well-scoped under g, i.e. ones that don't contain any Var subterms with unbound identifiers.
data Term : (d : Nat) -> (g : Vect n String) -> Type where
  Var : Elem v g -> Term d g
  Num : Nat -> Term d g
  Bool : Bool -> Term (2 + d) g
  Lam : Ty -> Term d (v :: g) -> Term (1 + d) g
  LamRec : Ty -> Ty -> Term d (vf :: v :: g) -> Term (1 + d) g
  (:$) : Term d g -> Term d g -> Term (1 + d) g
  If : Term d g -> Term d g -> Term d g -> Term (11 + d) g
  Tuple : Vect n (Term d g) -> Term (1 + d) g
  Variant : Nat -> Term d g -> Term (1 + d) g
  Case : Term d g -> Vect n (Term d g) -> Term (3 + d) g
  Unpack : {vs : Vect n String} -> Term d g -> Term d (vs ++ g) -> Term (1 + d) g
  As : Term d g -> Ty -> Term d g
  Let : Term (1 + d) g -> Term d (v :: g) -> Term (2 + d) g
