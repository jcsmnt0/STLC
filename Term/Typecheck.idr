module Typecheck

import Control.Catchable
import Data.Fin
import Data.Vect
import Data.Vect.Quantifiers

import Term.Scoped
import Term.Typed
import Ty.Raw
import Ty.Scoped

import Util.All
import Util.Dec
import Util.Elem
import Util.Ex
import Util.Vect

%default total

-- todo: make these useful
namespace TypeError
  data TypeError
    = App
    | If
    | Variant
    | LamRec
    | As (Scoped.Term d gv) Raw.Ty Raw.Ty
    | CantInfer
    | Case
    | Unpack

-- there has to be a better way
makeCaseTerm :
  (Monad m, Catchable m TypeError) =>
  {as : Vect n Raw.Ty} ->
  (p : n = n') ->
  SynTerm d 0 g (Sum as) ->
  All (\a => SynTerm d 0 g (a :-> b)) (replace {P = flip Vect Raw.Ty} p as) ->
  SynTerm (3 + d) 0 g b
makeCaseTerm {d = d} {g = g} {b = b} Refl t ts =
  Case t $
    map
      {p = \a => Term d 0 (map fromRawTy g) (fromRawTy a :-> fromRawTy b)}
      {q = \a => Term d 0 (map fromRawTy g) (a :-> fromRawTy b)}
      fromRawTy
      id
      ts

makeUnpackTerm :
  (Monad m, Catchable m TypeError) =>
  (p : n = n') ->
  SynTerm d 0 g (Tuple as) ->
  SynTerm d 0 (replace {P = flip Vect Raw.Ty} p as ++ g) b ->
  SynTerm (S d) 0 g b
makeUnpackTerm {d = d} {b = b} Refl s t =
  Unpack s $ replace {P = \g' => Term d 0 g' (fromRawTy b)} mapDistributesOverAppend t

mutual
  typecheck :
    (Monad m, Catchable m TypeError) =>
    {gv : Vect n String} ->
    (g : Vect n Raw.Ty) ->
    (s : Scoped.Term d gv) ->
    m (Ex $ SynTerm d 0 g)

  typecheck g (Var {v = v} i) =
    return $ E {x = index (toFin i) g} $
      replace
        {P = Term _ 0 (map fromRawTy g)}
        indexDistributesOverMap
        (Var (toFin i))

  typecheck g (Num n) =
    return $ E {x = NUM} $ C' n

  typecheck g (Bool b) =
    return $ E {x = BOOL} $ if b then true else false

  typecheck g (LamRec {d = d} a b t) =
    E {x = a :-> b} . LamRec <$> typecheckAgainst (a :-> b :: a :: g) t b (const TypeError.LamRec)

  typecheck g (Lam a t) = do
    E t' <- typecheck (a :: g) t
    return $ E {x = a :-> _} $ Lam t'

  typecheck g (s :$ t) = do
    E {x = a :-> b} s' <- typecheck g s | throw TypeError.App
    t' <- typecheckAgainst g t a (const TypeError.App)
    return $ E (s' :$ t')

  typecheck g (If s t u) = do
    s' <- typecheckAgainst g s (Sum [Tuple [], Tuple []]) (const TypeError.If)
    E {x = a} t' <- typecheck g t
    -- I think it might be a bug that assert_total is required here and for the Case case - d is decreasing
    u' <- assert_total $ typecheckAgainst g u a (const TypeError.If)
    return $ E $ If s' t' u'

  typecheck g (Tuple ts) = do
    ts' <- sequence $ map (typecheck g) ts
    return $ E {x = Tuple (map Ex.fst ts')} $ Tuple (map fromRawTy id (unzipEx ts'))

  typecheck g (Variant i s) =
    throw TypeError.Variant

  typecheck g (Variant i t `As` Sum {n = n} as) = do
    E {x = a} t' <- typecheck g t
    case natToFin i n of
      Just i' => case index i' as =? a of
        Yes p =>
          return $ E {x = Sum as} $ Variant (fromFin i' (map fromRawTy as)) $
            replace (sym (trans indexDistributesOverMap (cong p))) t'
        No _ => throw TypeError.Variant
      Nothing => throw TypeError.Variant

  typecheck {m = m} g (Case {n = n} t ts) = do
    E {x = Sum {n = n'} as} t' <- typecheck g t
      | throw TypeError.Case
    case n' =? n of
      Yes p => do
        E ts' <- assert_total $ typecheckCaseVect g (replace {P = flip Vect Raw.Ty} p as) ts
        return $ E $ makeCaseTerm {m = m} p t' ts'
      No _ => throw TypeError.Case

  typecheck {m = m} {n = gn} g (Unpack {d = d} {n = n} s t) = do
    E {x = Tuple {n = n'} as} s' <- typecheck g s | throw TypeError.Unpack
    case n' =? n of
      Yes p => do
        E t' <- assert_total $ typecheck (replace {P = flip Vect Raw.Ty} p as ++ g) t
        return $ E $ makeUnpackTerm {m = m} p s' t'
      No _ => throw TypeError.Unpack

  typecheck {m = m} g (t `As` a) =
    E <$> typecheckAgainst {m = m} g t a (TypeError.As t a)

  typecheck g (Let {v = v} s t) = do
    E {x = a} s' <- typecheck g s
    E t' <- typecheck (a :: g) t
    return $ E (Lam t' :$ s')

  typecheckAgainst :
    (Monad m, Catchable m TypeError) =>
    {gv : Vect n String} ->
    (g : Vect n Raw.Ty) ->
    Scoped.Term d gv ->
    (a : Raw.Ty) ->
    (Raw.Ty -> TypeError) ->
    m (SynTerm d 0 g a)
  typecheckAgainst g t a err = do
    E {x = a'} t' <- typecheck g t
    case a' =? a of
      Yes p => return $ replace p t'
      No _ => throw $ err a'

  typecheckCaseVect :
    (Monad m, Catchable m TypeError) =>
    {gv : Vect n String} ->
    (g : Vect n Raw.Ty) ->
    (as : Vect n' Raw.Ty) ->
    Vect n' (Scoped.Term d gv) ->
    m (Ex $ \b => All (\a => SynTerm d 0 g (a :-> b)) as)
  typecheckCaseVect g [] [] = return $ E {x = VOID} []
  typecheckCaseVect {d = d} g [a] [t] = do
    E {x = a' :-> b} t' <- typecheck g t | throw TypeError.Case
    case a' =? a of
      Yes p => return $ E {x = b} [replace {P = \a'' => SynTerm d 0 g (a'' :-> b)} p t']
      No _ => throw TypeError.Case
  typecheckCaseVect g (a :: as) (t :: ts) = do
    E {x = b} ts' <- typecheckCaseVect g as ts
    t' <- typecheckAgainst g t (a :-> b) (const TypeError.Case)
    return $ E (t' :: ts')
