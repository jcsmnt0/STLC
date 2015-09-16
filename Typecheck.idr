module Typecheck

import Control.Catchable
import Data.Fin
import Data.Vect

import PiVect
import Syntax
import Term
import Ty

import Util.Dec
import Util.Elem
import Util.Eq
import Util.Ex
import Util.Sigma

%default total

-- todo: make these useful
namespace TypeError
  data TypeError
    = App
    | If
    | Variant
    | LamRec
    | As (Scoped d gv) Ty Ty
    | CantInfer
    | Case
    | Unpack

-- todo: ewwwwwwwww
makeCaseTerm :
  (Monad m, Catchable m TypeError) =>
  {as : Vect n Ty} ->
  (p : n = n') ->
  Term d gty (Sum as) ->
  Vect n' String ->
  PiVect (\a => Term d (a :: gty) b) (replace {P = flip Vect Ty} p as) ->
  Term (S d) gty b
makeCaseTerm Refl tm vs tms = Case tm vs tms

makeUnpackTerm :
  (Monad m, Catchable m TypeError) =>
  {as : Vect n Ty} ->
  (p : n = n') ->
  Vect n' String ->
  Term (S d) gty (Tuple as) ->
  Term d (replace {P = flip Vect Ty} p as ++ gty) b ->
  Term (S d) gty b
makeUnpackTerm Refl vs s t = Unpack vs s t

mutual
  typecheck :
    (Monad m, Catchable m TypeError) =>
    {gv : Vect n String} ->
    (gty : Vect n Ty) ->
    (s : Scoped d gv) ->
    m (Ex (Term d gty))

  typecheck gty (Var {v = v} p) =
    return (E $ Var v (iso p gty))

  typecheck gty (Num n) =
    return (E $ Num n)

  typecheck gty (Bool b) =
    return (E $ Bool b)

  typecheck gty (LamRec {d = d} {vf = vf} {v = v} a b sc) = do
    E {x = b'} tm <- typecheck ((a :-> b) :: a :: gty) sc
    case b =? b' of
      Yes p => return (E $ LamRec vf v (replace {P = \x => Term d ((a :-> x) :: a :: gty) b'} p tm))
      No _ => throw TypeError.LamRec

  typecheck gty (Lam {v = v} a sc) = do
    E tm <- typecheck (a :: gty) sc
    return (E $ Lam v tm)

  typecheck gty (scx :$ scy) = do
    [E {x = a :-> b} tmx, E {x = c} tmy] <- typecheckVect gty [scx, scy]
      | _ => throw TypeError.App
    case a =? c of
      Yes p => return (E (tmx :$ rewrite p in tmy))
      No _ => throw TypeError.App

  typecheck gty (If {d = d} scx scy scz) = do
    -- doing these as three separate binds instead of with typecheckVect makes Idris typechecking reeeeally slow
    [E {x = Bool} tmx, E {x = a} tmy, E {x = b} tmz] <- typecheckVect gty [scx, scy, scz]
      | _ => throw TypeError.If
    case a =? b of
      Yes p => return (E $ If tmx tmy (replace {P = Term d gty} (sym p) tmz))
      No _ => throw TypeError.If

  typecheck gty (Tuple scs) = do
    tms <- typecheckVect gty scs
    return (E $ Tuple (unzip tms))

  typecheck gty (Variant i s) =
    throw TypeError.Variant -- has to be wrapped in an As

  typecheck gty (Variant i s `As` Sum {n = n} as) = do
    E {x = a} tm <- typecheck gty s
    case natToFin i n of
      Just i' => case index i' as =? a of
        Yes p => return (E $ Variant (fromFin i' as) (rewrite p in tm))
        No _ => throw TypeError.Variant
      Nothing => throw TypeError.Variant

  typecheck {m = m} gty (Case {n = n} {vs = vs} s ss) = do
    E {x = Sum {n = n'} as} tm <- typecheck gty s
      | throw TypeError.Case
    case n' =? n of
      Yes p => do
        (_ ** tms) <- assert_total (typecheckCaseVect gty (replace {P = flip Vect Ty} p as) ss)
        return (E $ makeCaseTerm {m = m} p tm vs tms)
      No _ => throw TypeError.Case

  typecheck {m = m} gty (Unpack {n = n} {vs = vs} s t) = do
    E {x = Tuple {n = n'} as} s' <- typecheck gty s
      | throw TypeError.Unpack
    case n' =? n of
      Yes p => do
        E t' <- assert_total (typecheck (replace {P = flip Vect Ty} p as ++ gty) t)
        return (E $ makeUnpackTerm {m = m} p vs s' t')
      No _ => throw TypeError.Unpack

  typecheck gty (s `As` ty) = do
    E {x = ty'} tm <- typecheck gty s
    case ty =? ty' of
      Yes _ => return (E tm)
      No _ => throw (As s ty ty')

  typecheck gty (Let {v = v} s t) = do
    E {x = a} s' <- typecheck gty s
    E t' <- typecheck (a :: gty) t
    return (E (Lam v t' :$ s'))

  typecheckVect :
    (Monad m, Catchable m TypeError) =>
    {gv : Vect n String} ->
    (gty : Vect n Ty) ->
    Vect n' (Scoped d gv) ->
    m (Vect n' (Ex (Term d gty)))
  typecheckVect gty scs = sequence (map (assert_total (typecheck gty)) scs)

  typecheckCaseVect :
    (Monad m, Catchable m TypeError) =>
    {gv : Vect n String} ->
    (gty : Vect n Ty) ->
    {vs : Vect n' String} ->
    (as : Vect n' Ty) ->
    PiVect (\v => Scoped d (v :: gv)) vs ->
    m (b ** PiVect (\a => Term d (a :: gty) b) as)
  typecheckCaseVect gty as [] = throw TypeError.Case
  typecheckCaseVect gty [] ss = throw TypeError.Case
  typecheckCaseVect gty [a] [s] = do
    E t <- catch {t = TypeError} (typecheck (a :: gty) s) (const (throw TypeError.Case))
    return (_ ** [t])
  typecheckCaseVect gty (a :: as) (s :: ss) = do
    E {x = b} t <- typecheck (a :: gty) s
    (b' ** ts) <- typecheckCaseVect gty as ss
    case b =? b' of
      Yes p => return (_ ** replace {P = Term _ (a :: gty)} p t :: ts)
      No _ => throw TypeError.Case
