module Syntax

import Data.Fin
import Data.Vect

import PVect
import Ty

%default total

infixl 5 :$

namespace Syn
  ||| Syntax without any scope or type information.
  ||| d is the (maximum) depth of the syntax tree, which provides functions that recurse over this structure with an
  ||| argument that decreases monotonically in size as they recurse down, which makes the termination checker happy -
  ||| otherwise things like "map (scopecheck gv)" don't pass as total.
  data Syn : (d : Nat) -> Type where
    Var : String -> Syn d
    Num : Double -> Syn d
    Bool : Bool -> Syn d
    Lam : String -> Ty -> Syn d -> Syn (S d)
    LamRec : String -> Ty -> String -> Ty -> Syn d -> Syn (S d)
    (:$) : Syn d -> Syn d -> Syn d
    If : Syn d -> Syn d -> Syn d -> Syn (S d)
    Tuple : Vect n (Syn d) -> Syn (S d)
    Variant : Nat -> Syn d -> Syn (S d)
    Case : Syn d -> Vect n (String, Syn d) -> Syn (S d)
    Unpack : Vect n String -> Syn (S d) -> Syn d -> Syn (S d)
    As : Syn d -> Ty -> Syn d
    Let : String -> Syn (S d) -> Syn d -> Syn (S d) -- Let is really a special case of Unpack

  depth : Syn d -> Nat
  depth {d = d} _ = d

namespace Scoped
  ||| Terms that are well-scoped under gv, i.e. ones that don't contain any Var subterms with unbound identifiers.
  data Scoped : (d : Nat) -> (gv : Vect n String) -> Type where
    Var : Elem v gv -> Scoped d gv
    Num : Double -> Scoped d gv
    Bool : Bool -> Scoped d gv
    Lam : Ty -> Scoped d (v :: gv) -> Scoped (S d) gv
    LamRec : Ty -> Ty -> Scoped d (vf :: v :: gv) -> Scoped (S d) gv
    (:$) : Scoped d gv -> Scoped d gv -> Scoped d gv
    If : Scoped d gv -> Scoped d gv -> Scoped d gv -> Scoped (S d) gv
    Tuple : Vect n (Scoped d gv) -> Scoped (S d) gv
    Variant : Nat -> Scoped d gv -> Scoped (S d) gv
    Case : {vs : Vect n String} -> Scoped d gv -> PVect (\v => Scoped d (v :: gv)) vs -> Scoped (S d) gv
    Unpack : {vs : Vect n String} -> Scoped (S d) gv -> Scoped d (vs ++ gv) -> Scoped (S d) gv
    As : Scoped d gv -> Ty -> Scoped d gv
    Let : Scoped (S d) gv -> Scoped d (v :: gv) -> Scoped (S d) gv
