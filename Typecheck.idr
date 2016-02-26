module Typecheck

import Control.Catchable
import Data.Fin
import Data.Vect
import Data.Vect.Quantifiers

import Syntax
import Term
import Ty

import Util.All
import Util.Dec
import Util.Elem
import Util.Eq
import Util.Ex
import Util.Sigma
import Util.Vect

%default total

hmmmm : Scoped (3 + d) gv
hmmmm = Variant 0 (Bool True) `As` Sum [BOOL, NUM]

-- todo: make these useful
namespace TypeError
  data TypeError
    = App
    | If
    | Variant
    | LamRec
    | As (Scoped d gv) SynTy SynTy
    | CantInfer
    | Case
    | Unpack

-- there has to be a better way
makeCaseTerm :
  (Monad m, Catchable m TypeError) =>
  {as : Vect n SynTy} ->
  (p : n = n') ->
  SynTerm d 0 gty (Sum as) ->
  All (\a => SynTerm d 0 gty (a :-> b)) (replace {P = flip Vect SynTy} p as) ->
  SynTerm (3 + d) 0 gty b
makeCaseTerm {d = d} {gty = gty} {b = b} Refl t ts =
  Case t $
    map
      {p = \a => Term d 0 (map fromSynTy gty) (fromSynTy a :-> fromSynTy b)}
      {q = \a => Term d 0 (map fromSynTy gty) (a :-> fromSynTy b)}
      fromSynTy
      id
      ts

makeUnpackTerm :
  (Monad m, Catchable m TypeError) =>
  (p : n = n') ->
  SynTerm d 0 gty (Tuple as) ->
  SynTerm d 0 (replace {P = flip Vect SynTy} p as ++ gty) b ->
  SynTerm (S d) 0 gty b
makeUnpackTerm {d = d} {b = b} Refl s t =
  Unpack s $ replace {P = \g' => Term d 0 g' (fromSynTy b)} mapDistributesOverAppend t

mutual
  typecheck :
    (Monad m, Catchable m TypeError) =>
    {gv : Vect n String} ->
    (gty : Vect n SynTy) ->
    (s : Scoped d gv) ->
    m (Ex $ SynTerm d 0 gty)

  typecheck gty (Var {v = v} i) =
    return $ E {x = index (toFin i) gty} $
      replace
        {P = Term _ 0 (map fromSynTy gty)}
        indexDistributesOverMap
        (Var (toFin i))

  typecheck gty (Num n) =
    return $ E {x = NUM} $ C' n

  typecheck gty (Bool b) =
    return $ E {x = BOOL} $ if b then true else false

  typecheck gty (LamRec {d = d} a b t) =
    E {x = a :-> b} . LamRec <$> typecheckAgainst (a :-> b :: a :: gty) t b (const TypeError.LamRec)

  typecheck gty (Lam a t) = do
    E t' <- typecheck (a :: gty) t
    return $ E {x = a :-> _} $ Lam t'

  typecheck gty (s :$ t) = do
    E {x = a :-> b} s' <- typecheck gty s | throw TypeError.App
    t' <- typecheckAgainst gty t a (const TypeError.App)
    return $ E (s' :$ t')

  typecheck gty (If s t u) = do
    s' <- typecheckAgainst gty s (Sum [Tuple [], Tuple []]) (const TypeError.If)
    E {x = a} t' <- typecheck gty t
    -- I think it might be a bug that assert_total is required here and for the Case case - d is decreasing
    u' <- assert_total $ typecheckAgainst gty u a (const TypeError.If)
    return $ E $ If s' t' u'

  typecheck gty (Tuple ts) = do
    ts' <- sequence $ map (typecheck gty) ts
    return $ E {x = Tuple (map Ex.fst ts')} $ Tuple (map fromSynTy id (unzipEx ts'))

  typecheck gty (Variant i s) =
    throw TypeError.Variant

  typecheck gty (Variant i t `As` Sum {n = n} as) = do
    E {x = a} t' <- typecheck gty t
    case natToFin i n of
      Just i' => case index i' as =? a of
        Yes p =>
          return $ E {x = Sum as} $ Variant (fromFin i' (map fromSynTy as)) $
            replace (sym (Eq.trans indexDistributesOverMap (cong p))) t'
        No _ => throw TypeError.Variant
      Nothing => throw TypeError.Variant

  typecheck {m = m} gty (Case {n = n} t ts) = do
    E {x = Sum {n = n'} as} t' <- typecheck gty t
      | throw TypeError.Case
    case n' =? n of
      Yes p => do
        E ts' <- assert_total $ typecheckCaseVect gty (replace {P = flip Vect SynTy} p as) ts
        return $ E $ makeCaseTerm {m = m} p t' ts'
      No _ => throw TypeError.Case

  typecheck {m = m} {n = gn} gty (Unpack {d = d} {n = n} s t) = do
    E {x = Tuple {n = n'} as} s' <- typecheck gty s | throw TypeError.Unpack
    case n' =? n of
      Yes p => do
        E t' <- assert_total $ typecheck (replace {P = flip Vect SynTy} p as ++ gty) t
        return $ E $ makeUnpackTerm {m = m} p s' t'
      No _ => throw TypeError.Unpack

  typecheck {m = m} gty (t `As` a) =
    E <$> typecheckAgainst {m = m} gty t a (As t a)

  typecheck gty (Let {v = v} s t) = do
    E {x = a} s' <- typecheck gty s
    E t' <- typecheck (a :: gty) t
    return $ E (Lam t' :$ s')

  typecheckAgainst :
    (Monad m, Catchable m TypeError) =>
    {gv : Vect n String} ->
    (gty : Vect n SynTy) ->
    Scoped d gv ->
    (a : SynTy) ->
    (SynTy -> TypeError) ->
    m (SynTerm d 0 gty a)
  typecheckAgainst gty t a err = do
    E {x = a'} t' <- typecheck gty t
    case a' =? a of
      Yes p => return $ replace p t'
      No _ => throw $ err a'

  typecheckCaseVect :
    (Monad m, Catchable m TypeError) =>
    {gv : Vect n String} ->
    (gty : Vect n SynTy) ->
    (as : Vect n' SynTy) ->
    Vect n' (Scoped d gv) ->
    m (Ex $ \b => All (\a => SynTerm d 0 gty (a :-> b)) as)
  typecheckCaseVect gty [] [] = return $ E {x = VOID} []
  typecheckCaseVect {d = d} gty [a] [t] = do
    E {x = a' :-> b} t' <- typecheck gty t | throw TypeError.Case
    case a' =? a of
      Yes p => return $ E {x = b} [replace {P = \a'' => SynTerm d 0 gty (a'' :-> b)} p t']
      No _ => throw TypeError.Case
  typecheckCaseVect gty (a :: as) (t :: ts) = do
    E {x = b} ts' <- typecheckCaseVect gty as ts
    t' <- typecheckAgainst gty t (a :-> b) (const TypeError.Case)
    return $ E (t' :: ts')
