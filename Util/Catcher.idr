module Util.Catcher

import Control.Catchable
import Control.Monad.Trans
import Data.Vect

import PVect
import Util.Elem

%default total

data Catcher : Vect n Type -> Type -> Type where
  Return : b -> Catcher as b
  Throw : Elem a as -> a -> Catcher as b

handle : PVect (\a => a -> b) as -> Catcher as b -> b
handle _ (Return x) = x
handle {as = []} _ (Throw Here x) impossible
handle (f :: _) (Throw Here x) = f x
handle (_ :: fs) (Throw (There p) x) = handle fs (Throw p x)

instance Functor (Catcher as) where
  map f (Return x) = Return (f x)
  map _ (Throw p x) = Throw p x

instance Applicative (Catcher as) where
  pure = Return

  (Return f) <*> (Return x) = Return (f x)
  (Throw p x) <*> _ = Throw p x
  _ <*> (Throw p x) = Throw p x

instance Monad (Catcher as) where
  (Return x) >>= f = f x
  (Throw p x) >>= _ = Throw p x

catchElem : Elem a as -> Catcher as b -> (a -> c) -> Maybe c
catchElem Here (Throw Here x) f = Just (f x)
catchElem {b = b} (There p) (Throw (There q) x) f = catchElem p (Throw {b = b} q x) f
catchElem _ _ _ = Nothing

class Element (n : Nat) (x : a) (xs : Vect n a) where
  somewhere : Elem x xs

instance Element (S n) x (x :: xs) where
  somewhere = Here

instance Element (S n) x xs => Element (S (S n)) x (y :: xs) where
  somewhere = There somewhere

instance Element n a as => Catchable (Catcher as) a where
  throw = Throw somewhere -- just on the floor or whatever
  catch x = fromMaybe x . catchElem somewhere x

record CatcherT (as : Vect n Type) (m : Type -> Type) (b : Type) where
  constructor CT
  runCatcherT : m (Catcher as b)

instance MonadTrans (CatcherT as) where
  lift = CT . map Return

instance Functor m => Functor (CatcherT as m) where
  map f = CT . map (map f) . runCatcherT

instance Applicative m => Applicative (CatcherT as m) where
  pure = CT . pure . Return
  (CT f) <*> (CT x) = CT [| f <*> x |]

instance Monad m => Monad (CatcherT as m) where
  (CT x) >>= f = CT $ do
    case !x of
      Return x' => runCatcherT (f x')
      Throw p x' => return (Throw p x')

instance (Element n a as, Monad m) => Catchable (CatcherT as m) a where
  throw = CT . pure . throw

  -- I think this can be done with just Applicative
  catch (CT x) f = CT $ do maybe x runCatcherT (catchElem somewhere !x f)
