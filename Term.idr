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
      Double ->
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
      Term d g (Tuple as) ->
      Term d (as ++ g) b ->
      Term (S d) g b

    Prim :
      (as : Vect n Ty) ->
      (b : Ty) ->
      (f : PVect Val as -> Partial (Val b)) ->
      Term d g (Tuple as) ->
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
      Term (S d) g a

    If :
      Term d g Bool ->
      Term d g a ->
      Term d g a ->
      Term (S d) g a

eval : PVect Val g -> Term d g a -> Partial (Val a)

eval p (Bool x) = Now x

eval p (Num x) = Now x

eval p (Tuple ts) = sequence (mapId (eval p) ts)

eval p (Variant e t) = Inj (map Val e) <$> eval p t

eval {g = g} p (Case t vs cs) = do
  Inj e x <- eval p t
  evalCase e x cs
where
  evalCase : Elem a (map Val as) -> a -> PVect (\b => Term d (b :: g) c) as -> Partial (Val c)
  evalCase Here x (c :: cs) = eval (x :: p) c
  evalCase (There p) x (c :: cs) = evalCase p x cs

eval p (Unpack vs ss t) = do
  xs <- eval p ss
  eval (xs ++ p) t

eval p (Prim as b f ts) = eval p ts >>= f

eval p (Var v i) = Now (indexElem i p)

eval p (Lam v t) = Now (\x => eval (x :: p) t)

eval p (LamRec {a = a} {b = b} vf v t) = Now (\x => eval (recurse :: x :: p) t)
  where
    recurse : Val a -> Partial (Val b)
    recurse x = Later (Later (eval p (LamRec vf v t)) >>= flip apply x)

eval p (s :$ t) = do
  f <- eval p s
  x <- eval p t
  f x

eval p (If s t u) = do
  b <- eval p s
  if b then eval p t else eval p u
