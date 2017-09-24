module Term.Eval

import Data.Vect
import Data.Vect.Quantifiers

import Term.Typed
import Ty.Scoped
import Ty.Val

import Util.All
import Util.Elem
import Util.Partial
import Util.Union

%default total

mutual
  -- this does pass the totality checker (modulo the one assert_total call in the Case case) but it takes
  -- a loooong time to do so, at least on my desktop
  export
  eval : (e : Vect l Type) -> Env e g -> Term d l g a -> Partial (Val e a)
  eval e p (C x) = x
  eval e p (Var i) = Now $ index i p
  eval e (_ :: p) (Weaken t) = eval e p t
  eval e p (Deepen t) = eval e p t
  eval e p (Lam t) = Now $ \x => eval e (x :: p) t
  eval e p (LamRec {a = a} {b = b} t) = Now $ \x => eval e (recurse :: x :: p) t
    where
      recurse : Val e a -> Partial (Val e b)
      recurse x = Later (Later (assert_total $ eval e p (LamRec t)) >>= flip apply x)
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
    -- add assert_total to make the totality checking a little faster
    f <- assert_total $ indexCase e p i ts
    -- I'm not sure why this isn't accepted as total - d is obviously decreasing?
    f' <- assert_total $ eval {d = 2 + d} e p f
    f' t'

  -- there's probably a way to not need this
  normalizeFunction :
    (e : Vect l Type) ->
    Env e g ->
    Term d l g (a :-> b) ->
    Partial (Term (2 + d) l g (normalize e a :-> normalize e b))
  normalizeFunction e p t = do
    t' <- eval e p t
    pure $ Lam $ Prim (C . t') (Var 0)

  indexCase :
    (e : Vect l Type) ->
    Env e g ->
    Elem a (map (Val e) as) ->
    All (\a' => Term d l g (a' :-> b)) as ->
    Partial (Term (2 + d) l g (C a :-> normalize e b))
  indexCase {as = _ :: _} e p Here (t :: _) = normalizeFunction e p t
  indexCase {as = _ :: _} e p (There i) (_ :: ts) = indexCase e p i ts
