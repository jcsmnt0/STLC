module Either

import Control.Catchable
import Control.Monad.Trans

%default total

(<|>) : Either a b -> Either a b -> Either a b
(Right x) <|> _ = Right x
(Left _) <|> y = y

mapLeft : (a -> b) -> Either a c -> Either b c
mapLeft f (Left x) = Left (f x)
mapLeft _ (Right y) = Right y

collapseEither : Either a a -> a
collapseEither = either id id

namespace EitherT
  record EitherT a (m : Type -> Type) b where
    constructor ET
    runEitherT : m (Either a b)

MonadTrans (EitherT a) where
  lift = ET . map Right

Functor m => Functor (EitherT a m) where
  map f (ET x) = ET $ map (map f) x

Applicative m => Applicative (EitherT a m) where
  pure = ET . pure . Right

  (ET f) <*> (ET x) = ET $ (<*>) <$> f <*> x

Monad m => Monad (EitherT a m) where
  (ET x) >>= f = ET $ do
    x' <- map (map f) x
    case x' of
      Left x'' => return (Left x'')
      Right x'' => runEitherT x''

Monad m => Catchable (EitherT e m) e where
  throw = ET . pure . Left

  catch (ET x) f = ET $ do
    x' <- x
    case x' of
      Right x'' => x
      Left x'' => runEitherT (f x'')
