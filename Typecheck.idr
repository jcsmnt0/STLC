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
  returnEx (Var v (snd (iso p gty)))

typecheck gty (Num n) =
  returnEx (Num n)

typecheck gty (Bool b) =
  returnEx (Bool b)

typecheck gty (Lam {v = v} t scx) = do
  E tmx <- typecheck (t :: gty) scx
  returnEx (Lam v tmx)

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
  returnEx (Tuple (unzip tms))

typecheck gty (Variant {a = a} ety sc) with (typecheck gty sc)
  typecheck gty (Variant {a = a} ety sc) | (Just (E {x = b} tm)) with (a =? b)
    typecheck gty (Variant ety sc) | (Just (E tm)) | Yes Refl = Just (E $ Variant ety tm)
    typecheck _ _ | _ | No _ = Nothing
  typecheck _ _ | Nothing = Nothing
