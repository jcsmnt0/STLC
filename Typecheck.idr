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

typecheck :
  {gv : Vect n String} ->
  (gty : Vect n Ty) ->
  (s : Scoped d gv) ->
  Maybe (Ex (Term d gty))

typecheck gty (Var {v = v} p) =
  return (E $ Var v (snd (iso p gty)))

typecheck gty (Num n) =
  return (E $ Num n)

typecheck gty (Bool b) =
  return (E $ Bool b)

typecheck gty (Lam {v = v} t scx) = do
  E tmx <- typecheck (t :: gty) scx
  return (E $ Lam v tmx)

typecheck gty (scx :$ scy) with (typecheck gty scx, typecheck gty scy)
  typecheck _ _ | (Just (E {x = a :-> b} tmx), Just (E {x = c} tmy)) with (a =? c)
    typecheck _ _ | (Just (E tmx), Just (E tmy)) | Yes Refl = Just (E (tmx :$ tmy))
    typecheck _ _ | _ | No _ = Nothing
  typecheck _ _ | _ = Nothing

typecheck gty (If scx scy scz) with (typecheck gty scx, typecheck gty scy, typecheck gty scz)
  typecheck _ _ | (Just (E {x = Bool} tmx), Just (E {x = a} tmy), Just (E {x = b} tmz)) with (a =? b)
    typecheck _ _ | (Just (E tmx), Just (E tmy), Just (E tmz)) | Yes Refl = Just (E $ If tmx tmy tmz)
    typecheck _ _ | _ | No _ = Nothing
  typecheck _ _ | _ = Nothing

typecheck gty (Tuple scs) = do
  tms <- sequence (map (typecheck gty) scs)
  return (E $ Tuple (unzip tms))

-- also: typecheck gty (s `As` Sum tys) fallthrough for inference!
typecheck gty (Variant i s `As` Sum {n = n} tys) with (typecheck gty s, natToFin i n)
  typecheck _ (Variant i s `As` Sum {n = n} tys) | (Just (E {x = ty} tm), Just i') with (ty =? index i' tys)
    typecheck _ (Variant i s `As` Sum {n = n} tys) | (Just (E tm), Just i') | Yes Refl =
      Just (E $ Variant (fromFin i' tys) tm)
    typecheck _ (Variant i s `As` Sum {n = n} tys) | (Just (E tm), Just i') | No _ = Nothing
  typecheck _ _ | _ = Nothing

typecheck gty (s `As` ty) = do
  E {x = ty'} tm <- typecheck gty s
  case ty =? ty' of
    Yes _ => Just (E tm)
    No _ => Nothing

typecheck gty (Variant i s) =
  Nothing -- has to be wrapped in an As

-- typecheck gty (Variant {a = a} ety sc) with (typecheck gty sc)
--   typecheck gty (Variant {a = a} ety sc) | (Just (E {x = b} tm)) with (a =? b)
--     typecheck gty (Variant ety sc) | (Just (E tm)) | Yes Refl = Just (E $ Variant ety tm)
--     typecheck _ _ | _ | No _ = Nothing
--   typecheck _ _ | Nothing = Nothing
