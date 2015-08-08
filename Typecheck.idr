module Typecheck

import Data.Fin
import Data.Vect

import PiVect
import Syntax
import Term
import Ty

import Util.Dec
import Util.Elem
import Util.Sigma

%default total

typecheck :
  {gv : Vect n String} ->
  (gty : Vect n Ty) ->
  (s : Scoped d gv) ->
  Maybe (t ** Term d gty t)

typecheck gty (Var {v = v} p) =
  return (_ ** Var v (snd (iso p gty)))

typecheck gty (Num n) =
  return (_ ** Num n)

typecheck gty (Bool b) =
  return (_ ** Bool b)

typecheck gty (Lam {v = v} t scx) = do
  (_ ** tmx) <- typecheck (t :: gty) scx
  return (_ ** Lam v tmx)

typecheck gty (scx :$ scy) with (typecheck gty scx, typecheck gty scy)
  typecheck _ _ | (Just (a :-> b ** tmx), Just (c ** tmy)) with (a =? c)
    typecheck _ _ | (Just (_ ** tmx), Just (_ ** tmy)) | Yes Refl = Just (_ ** tmx :$ tmy)
    typecheck _ _ | _ | No _ = Nothing
  typecheck _ _ | _ = Nothing

typecheck gty (If scx scy scz) with (typecheck gty scx, typecheck gty scy, typecheck gty scz)
  typecheck _ _ | (Just (Bool ** tmx), Just (a ** tmy), Just (b ** tmz)) with (a =? b)
    typecheck _ _ | (Just (Bool ** tmx), Just (a ** tmy), Just (a ** tmz)) | Yes Refl = Just (_ ** If tmx tmy tmz)
    typecheck _ _ | _ | No _ = Nothing
  typecheck _ _ | _ = Nothing

typecheck gty (Tuple scs) = do
  tms <- sequence (map (typecheck gty) scs)
  return (_ ** Tuple (fromSigmas tms))
