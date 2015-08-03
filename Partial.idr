module Control.Monad.Partial

%default total

codata Partial : Type -> Type where
  Now : a -> Partial a
  Later : Partial a -> Partial a

uncongNow : Now x = Now y -> x = y
uncongNow Refl = Refl

namespace Eventually
  codata Eventually : (a -> Type) -> Partial a -> Type where
    Now : p x -> Eventually p (Now x)
    Later : Eventually p (Force x) -> Eventually p (Later x)

hurry : Eventually p (Later x_) -> Eventually p x_
hurry (Now p) impossible
hurry (Later p) = p

partial impatience : Partial a -> a
impatience (Now x) = x
impatience (Later x) = impatience x

never : Partial a
never = Later never

instance Functor Partial where
  map f (Now x) = Now (f x)
  map f (Later x) = Later (map f x)

instance Applicative Partial where
  pure = Now

  (Now f) <*> x = map f x
  (Later f) <*> x = Later (f <*> x)

instance Monad Partial where
  (Now x) >>= f = f x
  (Later x) >>= f = Later (x >>= f)

lemma : Delay (Force x) = x
lemma = Refl

namespace strictPartialEq
  infixl 5 =~=
  codata (=~=) : Partial a -> Partial a -> Type where
    Now : Now x =~= Now x
    Later : x =~= y -> Later x =~= Later y

  -- id : (x : Partial a) -> x =~= x
  -- id (Now _) = Now
  -- id (Later x) = replace {P = \x => Later x =~= Later x} (sym lemma) (strictPartialEq.Later (id x))
  -- id Fail = e

namespace partialEq
  infixl 5 ~~
  data (~~) : Partial a -> Partial a -> Type where
    Now : Now x ~~ Now x
    Later : Inf (Force x ~~ Force y) -> Later x ~~ Later y
    LaterL : Force x ~~ y -> Later x ~~ y
    LaterR : x ~~ Force y -> x ~~ Later y

  subst : {P : a -> Type} -> x ~~ y -> Eventually P x -> Eventually P y
  subst Now p = p
  subst (Later eq) p = Later (subst eq (hurry p))
  subst (LaterL eq) p = subst eq (hurry p)
  subst (LaterR eq) p = Later (subst eq p)

Total : Partial a -> Type
Total p = (x ** p ~~ Now x)

namespace partialGte
  infixl 5 >=~ 
  data (>=~) : Partial a -> Partial a -> Type where
    Now : Now x >=~ Now x
    Later : Inf (Force x >=~ Force y) -> Later x >=~ Later y
    LaterL : Force x >=~ y -> Later x >=~ y

  subst : {P : a -> Type} -> x >=~ y -> Eventually P x -> Eventually P y
  subst Now p = p
  subst (Later eq) p = Later (subst eq (hurry p))
  subst (LaterL eq) p = subst eq (hurry p)

namespace PartialT
  codata PartialT : (Type -> Type) -> Type -> Type where
    Now : m a -> PartialT m a
    Later : PartialT m a -> PartialT m a

instance Functor f => Functor (PartialT f) where
  map f (Now x) = Now (map f x)
  map f (Later x) = Later (map f x)

instance Applicative f => Applicative (PartialT f) where
  pure = Now . pure

  (Now f) <*> (Now x) = Now (f <*> x)
  f <*> (Later x) = Later (f <*> x)
  (Later f) <*> x = Later (f <*> x)

namespace inTime
  data InTime : Partial a -> Nat -> Type where
    Now : (x : a) -> InTime (Now x) n
    Later : InTime x_ n -> InTime (Later x_) (S n)

instance Uninhabited (InTime (Later _) 0) where
  uninhabited (Later _) impossible

safeImpatience : {x_ : Partial a} -> (n : Nat) -> InTime x_ n -> a
safeImpatience _ (Now x) = x
safeImpatience (S n) (Later x_) = safeImpatience n x_
