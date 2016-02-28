module Term.Raw

import Data.Vect

import Ty.Raw

%default total

infixl 9 :$

-- d is the (maximum) depth of the syntax tree, which provides functions that recurse over this structure with an
-- argument that decreases monotonically in size as they recurse down, which makes the termination checker happy;
-- this comes up most often when trying to use a partially-applied recursive call as a function argument to e.g. map.
-- some constructors add more than 1 to the depth because the corresponding Scoped.Term and/or Typed.Term value is
-- actually a compound term that involves multiple constructors, and the scopechecking and typechecking operations
-- output a term with the same depth as their input argument, but that's probably avoidable.
data Term : (d : Nat) -> Type where
  Var : String -> Term d
  Num : Nat -> Term d
  Bool : Bool -> Term (2 + d)
  Lam : String -> Ty -> Term d -> Term (1 + d)
  LamRec : String -> String -> Ty -> Ty -> Term d -> Term (1 + d)
  (:$) : Term d -> Term d -> Term (1 + d)
  If : Term d -> Term d -> Term d -> Term (11 + d)
  Tuple : Vect n (Term d) -> Term (1 + d)
  Variant : Nat -> Term d -> Term (1 + d)
  Case : Term d -> Vect n (Term d) -> Term (3 + d)
  Unpack : Vect n String -> Term d -> Term d -> Term (1 + d)
  As : Term d -> Ty -> Term d
  Let : String -> Term (1 + d) -> Term d -> Term (2 + d)
