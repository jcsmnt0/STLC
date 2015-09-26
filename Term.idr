module Term

import Data.Fin
import Data.Vect

import Partial
import PVect
import Ty

import Util.Elem
import Util.Ex
import Util.Monad
import Util.Union

%default total

infixl 5 :$

namespace Term
  data Term : Nat -> Vect n Ty -> Ty -> Type where
    Bool :
      Bool ->
      Term d g Bool

    Num :
      Float ->
      Term d g Num

    Tuple :
      PVect (Term d g) as ->
      Term (S d) g (Tuple as)

    Variant :
      Elem a as ->
      Term d g a ->
      Term (S d) g (Sum as)

    Case :
      {as : Vect n Ty} ->
      Term d g (Sum as) ->
      Vect n String ->
      PVect (\a => Term d (a :: g) b) as ->
      Term (S d) g b

    Unpack :
      Vect n String ->
      Term (S d) g (Tuple as) ->
      Term d (as ++ g) b ->
      Term (S d) g b

    Prim :
      (as : Vect n Ty) ->
      (b : Ty) ->
      (f : PVect toType as -> Partial (toType b)) ->
      PVect (Term d g) as ->
      Term (S d) g b

    Var :
      String ->
      Elem a g ->
      Term d g a

    Lam :
      String ->
      Term d (a :: g) b ->
      Term (S d) g (a :-> b)

    LamRec :
      String ->
      String ->
      Term d ((a :-> b) :: a :: g) b ->
      Term (S d) g (a :-> b)

    (:$) :
      Term d g (b :-> a) ->
      Term d g b ->
      Term d g a

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
      PVect Val as ->
      Val (Tuple as)

    Variant :
      Elem a as ->
      Val a ->
      Val (Sum as)

    Cls :
      String ->
      PVect Val g ->
      Term d (a :: g) b ->
      Val (a :-> b)
    
    ClsRec :
      String ->
      String ->
      PVect Val g ->
      Term d ((a :-> b) :: a :: g) b ->
      Val (a :-> b)

mutual
  -- I think at least some of these assert_totals go away if Ty is tagged with its depth
  reflect : Val a -> toType a
  reflect {a = Bool} (Bool x) = x
  reflect {a = Num} (Num x) = x
  reflect {a = Tuple as} (Tuple xs) = mapId (assert_total reflect) xs
  reflect {a = Sum []} (Variant p t) = absurd p
  reflect {a = Sum (a :: as)} (Variant Here t) = Inj Here (reflect t)
  reflect {a = Sum (a :: as)} (Variant (There p) t) =
    let Inj p x = assert_total (reflect (Variant p t)) in
      Inj (There p) x
  reflect {a = a :-> b} (Cls v p tm) = \x => reflect <$> eval (unreflect x :: p) tm
  reflect {a = a :-> b} cls@(ClsRec f v p tm) = \x => reflect <$> Later (eval (cls :: unreflect x :: p) tm)

  unreflect : toType a -> Val a
  unreflect {a = Bool} x = Bool x
  unreflect {a = Num} x = Num x
  unreflect {a = Tuple as} xs = Tuple (mapId (assert_total unreflect) xs)
  unreflect {a = Sum (a :: as)} (Inj Here x) = Variant Here (assert_total (unreflect x))
  unreflect {a = Sum (a :: as)} (Inj (There p) x) =
    let Variant p t = assert_total (unreflect {a = Sum as} (Inj p x)) in
      Variant (There p) t
  unreflect {a = a :-> b} f =
    Cls {d = 1} "<unreflected value>" [] (Prim [a] b (\[x] => f x) [Var "<unreflected var>" Here])

  evalPVect : PVect Val g -> PVect (Term d g) as -> Partial (PVect Val as)
  evalPVect p = sequence . mapId (eval p)

  eval :
    PVect Val g ->
    Term d g a ->
    Partial (Val a)

  eval p (Bool x) =
    Now (Bool x)

  eval p (Num x) =
    Now (Num x)

  eval {g = g} p (Tuple xs) =
    Tuple <$> evalPVect p xs

  eval p (Variant e t) =
    Variant e <$> eval p t

  eval p (Case t vs cs) =
    eval p t >>= evalCase p cs
  where
    evalCase : PVect Val g -> PVect (\a => Term d (a :: g) b) as -> Val (Sum as) -> Partial (Val b)
    evalCase p (c :: _) (Variant Here v) = Later (eval (v :: p) c)
    evalCase p (_ :: cs) (Variant (There e) v) = evalCase p cs (Variant e v)

  eval p (Unpack vs tm1 tm2) = do
    Tuple xs <- eval p tm1
    eval (xs ++ p) tm2

  eval p (Prim as b f xs) =
    unreflect <$> join (f . mapId reflect <$> evalPVect p xs)

  eval p (Var v j) =
    Now (indexElem j p)

  eval p (Lam v t) =
    Now (Cls v p t)

  eval p (LamRec vf v t) =
    Now (ClsRec vf v p t)

  eval p (If b t f) = do
    Bool b' <- eval p b
    if b' then eval p t else eval p f

  eval p (s :$ t) =
    evalApp !(eval p s) !(eval p t)
    where
      evalApp : Val (a :-> b) -> Val a -> Partial (Val b)
      evalApp (Cls _ p s) t = Later (eval (t :: p) s)
      evalApp (ClsRec vf v p s) t = Later (eval (ClsRec vf v p s :: t :: p) s)
