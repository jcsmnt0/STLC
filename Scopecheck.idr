module Scopecheck

import Data.Vect

import Syntax
import Ty

import Util.Elem

%default total

scopecheck :
  (gv : Vect n String) ->
  (s : Syn d) ->
  Either String (Scoped d gv)

scopecheck gv (Num x) =
  return (Num x)

scopecheck gv (Bool x) =
  return (Bool x)

scopecheck gv (Var x) =
  case decElem x gv of
    Yes p => return (Var p)
    No _ => Left ("out of scope: " ++ x)

scopecheck gv (Lam v ty s) =
  [| (Lam ty) (scopecheck (v :: gv) s) |]

scopecheck gv (LamRec vf a v b s) =
  [| (LamRec a b) (scopecheck (vf :: v :: gv) s) |]

scopecheck gv (sx :$ sy) =
  [| scopecheck gv sx :$ scopecheck gv sy |]

scopecheck gv (If sx sy sz) =
  [| If (scopecheck gv sx) (scopecheck gv sy) (scopecheck gv sz) |]

scopecheck gv (Tuple ss) =
  [| Tuple (sequence (map (scopecheck gv) ss)) |]

scopecheck gv (Variant ty s) =
  [| (Variant ty) (scopecheck gv s) |]

scopecheck gv (s `As` ty) =
  [| (flip As ty) (scopecheck gv s) |]

unscope : Scoped d gv -> Syn d
unscope (Var {v = v} _) = Var v
unscope (Num x) = Num x
unscope (Bool x) = Bool x
unscope (Lam {v = v} ty s) = Lam v ty (unscope s)
unscope (LamRec {vf = vf} {v = v} a b s) = LamRec vf a v b (unscope s)
unscope (sx :$ sy) = unscope sx :$ unscope sy
unscope (If sb st sf) = If (unscope sb) (unscope st) (unscope sf)
unscope (Tuple ss) = Tuple (map unscope ss)
unscope (Variant ty s) = Variant ty (unscope s)
unscope (s `As` ty) = unscope s `As` ty
