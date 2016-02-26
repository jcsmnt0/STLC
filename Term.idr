module Term

import Data.Fin
import Data.HVect
import Data.Vect
import Data.Vect.Quantifiers

import Partial
import Syntax
import Ty

import Util.All
import Util.Elem
import Util.Ex
import Util.Func
import Util.Monad
import Util.Union
import Util.Vect

%default total

infixl 9 :$, @$

namespace Term
  data Term : Nat -> (l : Nat) -> Ty.Ctx l n -> Ty l -> Type where
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

  SynTerm : Nat -> Nat -> Vect n SynTy -> SynTy -> Type
  SynTerm d l g = Term d l (map fromSynTy g) . fromSynTy

  SynVal : Vect n Type -> SynTy -> Type
  SynVal e = Val e . fromSynTy

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

  mutual
    -- this does pass the totality checker (modulo the one assert_total call in the Case case) but it takes
    -- a loooong time to do so, at least on my desktop
    %assert_total
    eval : (e : Vect l Type) -> Ty.Env e g -> Term d l g a -> Partial (Val e a)
    eval e p (C x) = x
    eval e p (Var i) = Now $ index i p
    eval e (_ :: p) (Weaken t) = eval e p t
    eval e p (Deepen t) = eval e p t
    eval e p (Lam t) = Now $ \x => eval e (x :: p) t
    eval e p (LamRec {a = a} {b = b} t) = Now $ \x => eval e (recurse :: x :: p) t
      where
        recurse : Val e a -> Partial (Val e b)
        recurse x = Later (Later (eval e p (LamRec t)) >>= flip apply x)
    eval e p (s :$ t) = do
      s' <- eval e p s
      t' <- eval e p t
      s' t'
    eval e p (t :@ a) = betaExpandTy <$> eval (Val e a :: e) (weaken p) t
    eval e p (Prim f t) = eval e p t >>= eval e p . f
    eval e p (Tuple ts) = toHVect <$> sequenceMap' (eval e p) ts
    eval e p (Unpack s t) = do
      s' <- fromHVect <$> eval e p s
      eval e (s' ++ p) t
    eval e p (Variant i t) = Inj (map _ i) <$> eval e p t
    eval {d = S (S (S d))} e p (Case t ts) = do
      Inj i t' <- eval e p t
      f <- indexCase e p i ts
      -- I'm not sure why this isn't accepted as total - d is obviously decreasing?
      f' <- assert_total $ eval {d = 2 + d} e p f
      f' t'

    -- there's probably a way to not need this
    normalizeFunction :
      (e : Vect l Type) ->
      Ty.Env e g ->
      Term d l g (a :-> b) ->
      Partial (Term (2 + d) l g (normalize e a :-> normalize e b))
    normalizeFunction e p t = do
      t' <- eval e p t
      return $ Lam $ Prim (C . t') (Var 0)

    indexCase :
      (e : Vect l Type) ->
      Ty.Env e g ->
      Elem a (map (Val e) as) ->
      All (\a' => Term d l g (a' :-> b)) as ->
      Partial (Term (2 + d) l g (C a :-> normalize e b))
    indexCase {as = _ :: _} e p Here (t :: _) = normalizeFunction e p t
    indexCase {as = _ :: _} e p (There i) (_ :: ts) = indexCase e p i ts
