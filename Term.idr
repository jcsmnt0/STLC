module Term

import Data.Fin
import Data.Vect

import Partial
import PiVect
import Ty

%default total

namespace Pat
  data Pat : Type where
    Val :
      Pat

    Field :
      String ->
      Pat

    Index :
      Fin n ->
      Pat

    Prim :
      (argTys : Vect n BTy) ->
      (retTy : BTy) ->
      Func (map BTy.toType argTys) (BTy.toType retTy) ->
      Pat

namespace Match
  data Match : Pat -> Ty -> Ty -> Type where
    Val :
      Match Val a a

    Index :
      (i : Fin n) ->
      Match (Index i) (Tuple as) (Vect.index i as)

    Prim :
      (argTys : Vect n BTy) ->
      (retTy : BTy) ->
      (f : Func (map BTy.toType argTys) (BTy.toType retTy)) ->
      Match (Prim argTys retTy f) (Tuple (map toTy argTys)) (toTy retTy)

namespace Term
  infixl 5 :$
  data Term : Nat -> TyCtxt n -> Ty -> Type where
    Bool :
      Bool ->
      Term d g Bool

    Num :
      Float ->
      Term d g Num

    Tuple :
      PiVect (Term d g) as ->
      Term (S d) g (Tuple as)

    Variant :
      Elem a as ->
      Term d g a ->
      Term (S d) g (Sum as)

    Case :
      PiVect (\a => Term d (a :: g) b) as ->
      Term d g (Sum as) ->
      Term (S d) g b

    Match :
      Match p a b ->
      Term d g a ->
      Term d (b :: g) c ->
      Term (S d) g c

    Var :
      String ->
      Elem a g ->
      Term d g a

    Lam :
      String ->
      Term d (b :: g) a ->
      Term (S d) g (b :-> a)

    LamRec :
      Term d ((b :-> a) :: b :: g) a ->
      Term (S d) g (b :-> a)

    (:$) :
      Term d g (b :-> a) ->
      Term d g b ->
      Term (S d) g a

    If :
      Term d g Bool ->
      Term d g a ->
      Term d g a ->
      Term (S d) g a

namespace Val
  data Val : Ty -> Type where
    Bool :
      Bool ->
      Val Bool

    Num :
      Float ->
      Val Num

    Tuple :
      PiVect Val as ->
      Val (Tuple as)

    Variant :
      Elem a as ->
      Val a ->
      Val (Sum as)

    Cls :
      String ->
      PiVect Val g ->
      Term d (a :: g) b ->
      Val (a :-> b)

    ClsRec :
      PiVect Val g ->
      Term d ((a :-> b) :: a :: g) b ->
      Val (a :-> b)

  reify : Val (toTy a) -> BTy.toType a
  reify {a = Bool} (Bool x) = x
  reify {a = Num} (Num x) = x

  unreify : BTy.toType a -> Val (toTy a)
  unreify {a = Bool} = Bool
  unreify {a = Num} = Num

  extractMatch : Match p a b -> Val a -> Val b
  extractMatch Val v = v
  extractMatch (Index i) (Tuple vs) = index i vs
  extractMatch (Prim _ _ f) (Tuple vs) = unreify (applyPrim f vs)
    where
      applyPrim : Func (map BTy.toType as) (BTy.toType b) -> PiVect Val (map toTy as) -> BTy.toType b
      applyPrim {as = []} x [] = x
      applyPrim {as = _ :: _} f (x :: xs) = applyPrim (f (reify x)) xs

namespace eval
  eval :
    PiVect Val g ->
    Term d g a ->
    Partial (Val a)

  eval p (Bool x) =
    Now (Bool x)

  eval p (Num x) =
    Now (Num x)

  eval {g = g} p (Tuple xs) =
    Tuple <$> sequence {m = Partial} (mapId {q = Partial . Val} (eval p) xs)

  eval p (Variant e t) =
    Variant e <$> eval p t

  eval p (Case cs t) =
    eval p t >>= evalCase p cs
  where
    evalCase : PiVect Val g -> PiVect (\a => Term d (a :: g) b) as -> Val (Sum as) -> Partial (Val b)
    evalCase p (c :: _) (Variant Here v) = Later (eval (v :: p) c)
    evalCase p (_ :: cs) (Variant (There e) v) = evalCase p cs (Variant e v)

  eval p (Match m s t) =
    Later (eval (extractMatch m !(eval p s) :: p) t)

  eval p (Var v j) =
    Now (indexElem j p)

  eval p (Lam v t) =
    Now (Cls v p t)

  eval p (LamRec t) =
    Now (ClsRec p t)

  eval p (If b t f) = do
    Bool b' <- eval p b
    if b' then eval p t else eval p f

  eval p (s :$ t) =
    evalApp !(eval p s) !(eval p t)
    where
      evalApp : Val (a :-> b) -> Val a -> Partial (Val b)
      evalApp (Cls _ p t) v = Later (eval (v :: p) t)
      evalApp (ClsRec p t) v = Later (eval (ClsRec p t :: v :: p) t)
