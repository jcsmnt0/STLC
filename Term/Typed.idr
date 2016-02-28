module Term.Typed

import Data.Vect
import Data.Vect.Quantifiers

import Ty.Raw
import Ty.Scoped
import Ty.Val

import Util.Partial

%default total

infixl 9 :$, @$

data Term : Nat -> (l : Nat) -> Ctx l n -> Ty l -> Type where
  C :
    Partial a ->
    Term d l g (C a)

  Var :
    (i : Fin n) ->
    Term d l g (index i g)

  Weaken :
    Term d l g a ->
    Term d l (b :: g) a

  Deepen :
    Term d l g a ->
    Term (S d) l g a

  Lam :
    Term d l (a :: g) b ->
    Term (1 + d) l g (a :-> b)

  LamRec :
    Term d l (a :-> b :: a :: g) b ->
    Term (1 + d) l g (a :-> b)

  (:$) :
    Term d l g (a :-> b) ->
    Term d l g a ->
    Term (1 + d) l g b

  (:@) :
    Term d (S l) (weaken g) a ->
    (b : Ty l) ->
    Term (1 + d) l g (a :@ b)

  Prim :
    (a -> Term d l g b) ->
    Term d l g (C a) ->
    Term (1 + d) l g b

  Tuple :
    All (Term d l g) as ->
    Term (1 + d) l g (Tuple as)

  Unpack :
    Term d l g (Tuple as) ->
    Term d l (as ++ g) b ->
    Term (1 + d) l g b

  Variant :
    Elem a as ->
    Term d l g a ->
    Term (1 + d) l g (Sum as)

  Case :
    Term d l g (Sum as) ->
    All (\a => Term d l g (a :-> b)) as ->
    Term (3 + d) l g b -- +3 to account for the Lam and Prim in normalizeFunction during evaluation

SynTerm : Nat -> Nat -> Vect n Raw.Ty -> Raw.Ty -> Type
SynTerm d l g = Term d l (map fromRawTy g) . fromRawTy

(@$) : Term d (S l) (weaken g) (a :-> b) -> Term (1 + d) l g (a :@ c) -> Term (2 + d) l g (b :@ c)
s @$ t = (s :@ _) :$ t

deepenN : (n : Nat) -> Term d l g a -> Term (n + d) l g a
deepenN Z = id
deepenN (S n) = Deepen . deepenN n

C' : a -> Term d l g (C a)
C' = C . Now

unit : Term (1 + d) 0 g UNIT -- https://youtu.be/CaxDRF_TKjg
unit = Tuple []

true : Term (2 + d) 0 g BOOL
true = Variant Here unit

false : Term (2 + d) 0 g BOOL
false = Variant (There Here) unit

bool : Bool -> Term (2 + d) 0 g BOOL
bool x = if x then true else false

if' : Term (7 + d) 1 g (BOOL :-> LAZY 0 :-> LAZY 0 :-> 0)
if' = Lam $ Lam $ Lam $ Case (Var 2)
  [ Var 1
  , Var 0
  ]

If : Term d 0 g BOOL -> Term d 0 g a -> Term d 0 g a -> Term (11 + d) 0 g a
If s t u = (if' :@ _) :$ deepenN 8 s :$ deepenN 8 (Lam (Weaken t)) :$ deepenN 9 (Lam (Weaken u))
