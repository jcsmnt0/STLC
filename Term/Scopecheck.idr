module Scopecheck

import Control.Catchable
import Data.Vect
import Data.Vect.Quantifiers

import Term.Raw
import Term.Scoped
import Ty.Raw

import Util.Elem

%default total

scopecheck :
  (Applicative m, Catchable m String) =>
  (g : Vect n String) ->
  (t : Raw.Term d) ->
  m (Scoped.Term d g)

scopecheck g (Num x) =
  pure (Num x)

scopecheck g (Bool x) =
  pure (Bool x)

scopecheck g (Var i) =
  case decElem i g of
    Yes p => pure (Var p)
    No _ => throw ("out of scope: " ++ i)

scopecheck g (Lam v a t) =
  Lam {v = v} a <$> scopecheck (v :: g) t

scopecheck g (LamRec vf v a b t) =
  LamRec {vf = vf} {v = v} a b <$> scopecheck (vf :: v :: g) t

scopecheck g (s :$ t) =
  [| scopecheck g s :$ scopecheck g t |]

scopecheck g (If s t u) =
  [| If (scopecheck g s) (scopecheck g t) (scopecheck g u) |]

scopecheck g (Tuple ts) =
  [| Tuple (sequence (map (scopecheck g) ts)) |]

scopecheck g (Variant a t) =
  Variant a <$> scopecheck g t

scopecheck g (Case t ts) = do
  [| Case (scopecheck g t) (sequence (map (scopecheck g) ts)) |]

scopecheck g (Unpack vs t ts) =
  Unpack {vs = vs} <$> scopecheck g t <*> scopecheck (vs ++ g) ts

scopecheck g (t `As` a) =
  flip As a <$> scopecheck g t

scopecheck g (Let v s t) =
  Let {v = v} <$> scopecheck g s <*> scopecheck (v :: g) t

unscope : Scoped.Term d g -> Raw.Term d
unscope (Var {v = v} _) = Var v
unscope (Num x) = Num x
unscope (Bool x) = Bool x
unscope (Lam {v = v} a t) = Lam v a (unscope t)
unscope (LamRec {vf = vf} {v = v} a b t) = LamRec vf v a b (unscope t)
unscope (s :$ t) = unscope s :$ unscope t
unscope (If sb st sf) = If (unscope sb) (unscope st) (unscope sf)
unscope (Tuple ts) = Tuple (map unscope ts)
unscope (Variant a t) = Variant a (unscope t)
unscope (Case t ts) = Case (unscope t) (map unscope ts)
unscope (Unpack {vs = vs} t ts) = Unpack vs (unscope t) (unscope ts)
unscope (t `As` a) = unscope t `As` a
unscope (Let {v = v} s t) = Let v (unscope s) (unscope t)
