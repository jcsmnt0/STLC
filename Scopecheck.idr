module Scopecheck

import Control.Catchable
import Data.Vect

import PVect
import Syntax
import Ty

import Util.Elem

%default total

scopecheck :
  (Applicative m, Catchable m String) =>
  (gv : Vect n String) ->
  (s : Syn d) ->
  m (Scoped d gv)

scopecheck gv (Num x) =
  pure (Num x)

scopecheck gv (Bool x) =
  pure (Bool x)

scopecheck gv (Var x) =
  case decElem x gv of
    Yes p => pure (Var p)
    No _ => throw ("out of scope: " ++ x)

scopecheck gv (Lam v ty s) =
  Lam {v = v} ty <$> scopecheck (v :: gv) s

scopecheck gv (LamRec vf a v b s) =
  LamRec {vf = vf} {v = v} a b <$> scopecheck (vf :: v :: gv) s

scopecheck gv (sx :$ sy) =
  [| scopecheck gv sx :$ scopecheck gv sy |]

scopecheck gv (If sx sy sz) =
  If <$> scopecheck gv sx <*> scopecheck gv sy <*> scopecheck gv sz

scopecheck gv (Tuple ss) =
  Tuple <$> sequence (map (scopecheck gv) ss)

scopecheck gv (Variant ty s) =
  Variant ty <$> scopecheck gv s

scopecheck gv (Case s ss) =
  Case <$> scopecheck gv s <*> scopecheckCaseVect ss
  where
    scopecheckCaseVect :
      (Applicative m, Catchable m String) =>
      (xs : Vect n (String, Syn d)) ->
      m (PVect (\v => Scoped d (v :: gv)) (map (\x => fst x) xs))
    scopecheckCaseVect [] = pure []
    scopecheckCaseVect {n = S n} ((v, s) :: ss) =
      -- I'm pretty sure this is terminating because d is decreasing, but the typechecker doesn't see it
      [| assert_total (scopecheck (v :: gv) s) :: scopecheckCaseVect ss |]

scopecheck gv (Unpack vs s t) =
  Unpack {vs = vs} <$> scopecheck gv s <*> scopecheck (vs ++ gv) t

scopecheck gv (s `As` ty) =
  flip As ty <$> scopecheck gv s

scopecheck gv (Let v s t) =
  Let {v = v} <$> scopecheck gv s <*> scopecheck (v :: gv) t

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
unscope (Case s ss) = Case (unscope s) (unscopeCaseVect ss)
  where
    unscopeCaseVect : {vs : Vect n String} -> PVect (\v => Scoped d (v :: gv)) vs -> Vect n (String, Syn d)
    unscopeCaseVect [] = []
    -- same thing about totality here as with scopecheckCaseVect
    unscopeCaseVect ((::) {x = v} s ss) = (v, assert_total (unscope s)) :: unscopeCaseVect ss
unscope (Unpack {vs = vs} s t) = Unpack vs (unscope s) (unscope t)
unscope (s `As` ty) = unscope s `As` ty
unscope (Let {v = v} s t) = Let v (unscope s) (unscope t)
