module Typecheck

import Data.Fin
import Data.Vect

import PiVect
import Syntax
import Term
import Ty

import Util.Dec
import Util.Elem
import Util.Ex
import Util.Sigma

%default total

data TypeError
  = App
  | If
  | Variant
  | As (Scoped d gv) Ty Ty
  | Fix
  | CantInfer

typecheck :
  {gv : Vect n String} ->
  (gty : Vect n Ty) ->
  (s : Scoped d gv) ->
  Either TypeError (Ex (Term d gty))

typecheck gty (Var {v = v} p) =
  return (E $ Var v (iso p gty))

typecheck gty (Num n) =
  return (E $ Num n)

typecheck gty (Bool b) =
  return (E $ Bool b)

typecheck gty (Lam {v = v} t scx) = do
  E tmx <- typecheck (t :: gty) scx
  return (E $ Lam v tmx)

typecheck gty (scx :$ scy) with (typecheck gty scx, typecheck gty scy)
  typecheck _ _ | (Right (E {x = a :-> b} tmx), Right (E {x = c} tmy)) with (a =? c)
    typecheck _ _ | (Right (E tmx), Right (E tmy)) | Yes Refl = Right (E (tmx :$ tmy))
    typecheck _ _ | _ | No _ = Left App
  typecheck _ _ | _ = Left App

typecheck gty (If scx scy scz) with (typecheck gty scx, typecheck gty scy, typecheck gty scz)
  typecheck _ _ | (Right (E {x = Bool} tmx), Right (E {x = a} tmy), Right (E {x = b} tmz)) with (a =? b)
    typecheck _ _ | (Right (E tmx), Right (E tmy), Right (E tmz)) | Yes Refl = Right (E $ If tmx tmy tmz)
    typecheck _ _ | _ | No _ = Left If
  typecheck _ _ | _ = Left If

typecheck gty (Tuple scs) = do
  tms <- sequence (map (typecheck gty) scs)
  return (E $ Tuple (unzip tms))

-- also: typecheck gty (s `As` Sum tys) fallthrough for inference!
typecheck gty (Variant i s `As` Sum {n = n} tys) with (typecheck gty s, natToFin i n)
  typecheck _ (Variant i s `As` Sum {n = n} tys) | (Right (E {x = ty} tm), Just i') with (ty =? index i' tys)
    typecheck _ (Variant i s `As` Sum {n = n} tys) | (Right (E tm), Just i') | Yes Refl =
      Right (E $ Variant (fromFin i' tys) tm)
    typecheck _ (Variant i s `As` Sum {n = n} tys) | (Right (E tm), Just i') | No _ = Left Variant
  typecheck _ _ | _ = Left Variant

typecheck gty (s `As` ty) = do
  E {x = ty'} tm <- typecheck gty s
  case ty =? ty' of
    Yes _ => Right (E tm)
    No _ => Left (As s ty ty')

typecheck gty (Fix ty s) with (typecheck (ty :: gty) s)
  typecheck gty (Fix ty s) | (Right (E {x = ty'} tm)) with (ty =? ty')
    typecheck gty (Fix ty s) | (Right (E {x = ty} tm)) | Yes Refl = return (E $ Fix tm)
    typecheck _ _ | _ | No _ = Left Fix
  typecheck _ _ | _ = Left Fix

typecheck gty (Variant i s) =
  Left Variant -- has to be wrapped in an As
