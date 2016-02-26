module Syntax

import Data.Fin
import Data.Vect
import Data.Vect.Quantifiers

import Util.Dec
import Util.Vect

%default total

infixr 10 :->
infixl 9 :$

data SynTy
  = NUM
  | (:->) SynTy SynTy
  | Tuple (Vect n SynTy)
  | Sum (Vect n SynTy)

VOID : SynTy
VOID = Sum []

UNIT : SynTy
UNIT = Tuple []

BOOL : SynTy
BOOL = Sum [UNIT, UNIT]

LAZY : SynTy -> SynTy
LAZY a = UNIT :-> a

Requires (Tuple ss = Tuple ts) (ss ~=~ ts) where
  because contra Refl = contra Refl

Requires (Sum ss = Sum ts) (ss ~=~ ts) where
  because contra Refl = contra Refl

Requires (s :-> t = s' :-> t') (s = s') where
  because contra Refl = contra Refl

Requires (s :-> t = s' :-> t') (t = t') where
  because contra Refl = contra Refl

DecEq SynTy where
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

namespace Syn
  ||| Syntax without any scope or type information.
  ||| d is the (maximum) depth of the syntax tree, which provides functions that recurse over this structure with an
  ||| argument that decreases monotonically in size as they recurse down, which makes the termination checker happy -
  ||| otherwise things like "map (scopecheck gv)" don't pass as total.
  data Syn : (d : Nat) -> Type where
    Var : String -> Syn d
    Num : Nat -> Syn d
    Bool : Bool -> Syn (2 + d)
    Lam : String -> SynTy -> Syn d -> Syn (S d)
    LamRec : String -> SynTy -> String -> SynTy -> Syn d -> Syn (S d)
    (:$) : Syn d -> Syn d -> Syn (S d)
    If : Syn d -> Syn d -> Syn d -> Syn (11 + d)
    Tuple : Vect n (Syn d) -> Syn (S d)
    Variant : Nat -> Syn d -> Syn (S d)
    Case : Syn d -> Vect n (Syn d) -> Syn (3 + d)
    Unpack : Vect n String -> Syn d -> Syn d -> Syn (S d)
    As : Syn d -> SynTy -> Syn d
    Let : String -> Syn (S d) -> Syn d -> Syn (S (S d)) -- Let is really a special case of Unpack

  depth : Syn d -> Nat
  depth {d = d} _ = d

namespace Scoped
  ||| Terms that are well-scoped under gv, i.e. ones that don't contain any Var subterms with unbound identifiers.
  data Scoped : (d : Nat) -> (gv : Vect n String) -> Type where
    Var : Elem v gv -> Scoped d gv
    Num : Nat -> Scoped d gv
    Bool : Bool -> Scoped (2 + d) gv
    Lam : SynTy -> Scoped d (v :: gv) -> Scoped (S d) gv
    LamRec : SynTy -> SynTy -> Scoped d (vf :: v :: gv) -> Scoped (S d) gv
    (:$) : Scoped d gv -> Scoped d gv -> Scoped (S d) gv
    If : Scoped d gv -> Scoped d gv -> Scoped d gv -> Scoped (11 + d) gv
    Tuple : Vect n (Scoped d gv) -> Scoped (S d) gv
    Variant : Nat -> Scoped d gv -> Scoped (S d) gv
    Case : Scoped d gv -> Vect n (Scoped d gv) -> Scoped (3 + d) gv
    Unpack : {vs : Vect n String} -> Scoped d gv -> Scoped d (vs ++ gv) -> Scoped (S d) gv
    As : Scoped d gv -> SynTy -> Scoped d gv
    Let : Scoped (S d) gv -> Scoped d (v :: gv) -> Scoped (S (S d)) gv
