module Syntax

import Data.Fin
import Data.Vect

import PiVect
import Ty

%default total

infixl 5 :$

namespace Syn
  ||| Syntax without any scope or type information.
  ||| d is the depth of the syntax tree, which provides functions that recurse over this structure with an argument
  ||| that decreases monotonically in size as they recurse down, which makes the termination checker happy.
  data Syn : (d : Nat) -> Type where
    Var : String -> Syn d
    Num : Float -> Syn d
    Bool : Bool -> Syn d
    Lam : String -> Ty -> Syn d -> Syn (S d)
    (:$) : Syn d -> Syn d -> Syn (S d)
    If : Syn d -> Syn d -> Syn d -> Syn (S d)
    Tuple : Vect n (Syn d) -> Syn (S d)

  depth : Syn d -> Nat
  depth {d = d} _ = d

  lift : (m `LTE` n) -> Syn m -> Syn n
  lift p (Var v) = Var v
  lift p (Num x) = Num x
  lift p (Bool x) = Bool x
  lift (LTESucc p) (Lam v ty s) = Lam v ty (lift p s)
  lift (LTESucc p) (sx :$ sy) = lift p sx :$ lift p sy
  lift (LTESucc p) (If sb st sf) = If (lift p sb) (lift p st) (lift p sf)
  lift (LTESucc p) (Tuple ss) = Tuple (map (lift p) ss)

%name Syn sx, sy, sz

namespace Scoped
  ||| Terms that are well-scoped under gv, i.e. ones that don't contain any Var subterms with unbound identifiers.
  data Scoped : (d : Nat) -> (gv : Vect n String) -> Type where
    Var : Elem v gv -> Scoped d gv
    Num : Float -> Scoped d gv
    Bool : Bool -> Scoped d gv
    Lam : Ty -> Scoped d (v :: gv) -> Scoped (S d) gv
    (:$) : Scoped d gv -> Scoped d gv -> Scoped (S d) gv
    If : Scoped d gv -> Scoped d gv -> Scoped d gv -> Scoped (S d) gv
    Tuple : Vect n (Scoped d gv) -> Scoped (S d) gv

%name Scoped scx, scy, scz
