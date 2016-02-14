module Parser

import Control.Catchable
import Data.Vect

%access public

%default partial

-- resolution only works if I specify that it's not dependent on e - why?
interface Sequence s e | s where
  cons : e -> s -> s
  uncons : s -> Maybe (e, s)

Sequence String Char where
  cons = strCons
  uncons "" = Nothing
  uncons str = Just (assert_total (strHead str), assert_total (strTail str))


%default total

Sequence s Char => Sequence (Nat, s) Char where
  cons x (n, xs) = (n, cons x xs) -- pointless but rounds out the definition

  uncons (n, xs) =
    case uncons xs of
      Just ('\n', xs') => Just ('\n', (S n, xs'))
      Just (c, xs') => Just (c, (n, xs'))
      Nothing => Nothing

Sequence (List a) a where
  cons = (::)
  uncons [] = Nothing
  uncons (x :: xs) = Just (x, xs)

data Result : Type -> Type -> Type where
  MkResult : o -> s -> Result s o

Show o => Show (Result s o) where
  show (MkResult x _) = show x

Functor (Result i) where
  map f (MkResult x sf) = MkResult (f x) sf

output : Result i o -> o
output (MkResult x _) = x

data Parser : (Type -> Type) -> Type -> Type -> Type -> Type -> Type where
  MkParser : Sequence s i => (s -> m (Result s o)) -> Parser m e s i o

-- this is so the library parsers can throw strings as errors while letting higher level parsers use other kinds
-- of values as errors
interface ParseError e where
  fromString : String -> e

ParseError String where
  fromString = id

runParser : Catchable m e => Parser m e s i o -> s -> m (Result s o)
runParser (MkParser f) = f

execParser : (Functor m, Catchable m e) => Parser m e s i o -> s -> m o
execParser f xs = map output (runParser f xs)

(Monad m, Catchable m e, Sequence s i, Semigroup o) => Semigroup (Parser m e s i o) where
  p <+> q = MkParser $ \i => do
    MkResult op i' <- runParser p i
    MkResult oq i'' <- runParser q i'
    return (MkResult (op <+> oq) i'')

(Monad m, Catchable m e, Sequence s i, Monoid o) => Monoid (Parser m e s i o) where
  neutral = MkParser $ \i => return (MkResult neutral i)

(Functor m, Sequence s i) => Functor (Parser m e s i) where
  map f (MkParser g) = MkParser $ \i => map f <$> g i

(Monad m, Catchable m e, Sequence s i) => Applicative (Parser m e s i) where
  pure x = MkParser $ \i => return (MkResult x i)

  p <*> q = MkParser $ \i => do
    MkResult op i' <- runParser p i
    MkResult oq i'' <- runParser q i'
    return (MkResult (op oq) i'')

(Monad m, Catchable m e, Sequence s i) => Monad (Parser m e s i) where
  g >>= f = MkParser $ \i => do
    MkResult o i' <- runParser g i
    MkResult o' i'' <- runParser (f o) i'
    return (MkResult o' i'')

failWith : (Catchable m e, Sequence s i) => e -> Parser m e s i o
failWith err = MkParser (const (throw err))

propagate :
  (Catchable m e, Catchable m e', Sequence s i, ParseError e, ParseError e') =>
  (e -> e') ->
  Parser m e s i o ->
  Parser m e' s i o
propagate f p = MkParser $ \i => catch (runParser p i) (throw . f)

private throwStr : (Catchable m e, Sequence s i, ParseError e) => String -> Parser m e s i o
throwStr = failWith . fromString

private rethrowStr :
  (Catchable m e, Sequence s i, ParseError e, Semigroup e) =>
  String ->
  Parser m e s i o ->
  Parser m e s i o
rethrowStr x = propagate ((fromString x) <+>)

(Monad m, Catchable m e, Sequence s i, ParseError e) => Alternative (Parser m e s i) where
  empty = throwStr "empty"
  f <|> g = MkParser $ \i => catch {t = e} (runParser f i) (const (runParser g i))

choice : (Monad m, Catchable m e, Sequence s i, ParseError e) => Vect (S n) (Parser m e s i o) -> Parser m e s i o
choice ps = foldl1 (<|>) ps

noop : (Monad m, Catchable m e, Sequence s i, Monoid o) => Parser m e s i o
noop = neutral

any : (Monad m, Catchable m e, Sequence s i, ParseError e) => Parser m e s i i
any {e = e} = MkParser $ \i =>
  case uncons i of
    Nothing => throw {t = e} (fromString "any failed: no input")
    Just (x, xs) => return (MkResult x xs)

maybe : (Monad m, Catchable m e, Sequence s i, ParseError e) => Parser m e s i o -> Parser m e s i (Maybe o)
maybe {e = e} p = MkParser $ \i => catch {t = e} (runParser (Just <$> p) i) (const (return (MkResult Nothing i)))

matchMap : (Monad m, Catchable m e, Sequence s i, ParseError e) => (i -> Maybe o) -> Parser m e s i o
matchMap {e = e} f = MkParser $ \i =>
  case uncons i of
    Nothing => throw {t = e} (fromString "matchMap failed: no input")
    Just (x, xs) =>
      case f x of
        Nothing => throw {t = e} (fromString "matchMap failed: bad input")
        Just x => return (MkResult x xs)

match : (Monad m, Catchable m e, Sequence s i, ParseError e) => (i -> Bool) -> Parser m e s i i
match f = matchMap (\x => if f x then Just x else Nothing) <|> throwStr "match failed"

token : (Monad m, Catchable m e, Sequence s i, ParseError e, Eq i) => i -> Parser m e s i i
token x = match (== x) <|> throwStr "token failed"

covering string : (Monad m, Catchable m e, Sequence s i, Monoid s, ParseError e, Eq i) => s -> Parser m e s i s
string s =
  case uncons s of
    Nothing => noop
    Just (x, xs) => [| cons (token x) (string xs) |] <|> throwStr "string failed"

ignore : (Functor m, Catchable m e, Sequence s i) => Parser m e s i o -> Parser m e s i ()
ignore = map (const ())

covering many : (Monad m, Catchable m e, Sequence s i, ParseError e) => Parser m e s i o -> Parser m e s i (List o)
many p = do
  x <- maybe p
  case x of
    Nothing => return []
    Just x' => return (x' :: !(many p))

covering many' : (Monad m, Catchable m e, Sequence s i, ParseError e) => Parser m e s i o -> Parser m e s i ()
many' p = do
  x <- maybe p
  case x of
    Nothing => return ()
    Just _ => many' p

guard : (Monad m, Catchable m e, Sequence s i, ParseError e) => (o -> Bool) -> Parser m e s i o -> Parser m e s i o
guard f p = do
  x <- p
  if f x then return x else throwStr "guard failed"

iff : (Monad m, Catchable m e, Sequence s i, ParseError e) => Parser m e s i o -> (o -> Bool) -> Parser m e s i o
iff = flip guard

covering many1 :
  (Monad m, Catchable m e, Sequence s i, ParseError e, Semigroup e) =>
  Parser m e s i o ->
  Parser m e s i (List o)
many1 p = rethrowStr "many1: " $ guard (isSucc . length) (many p)

covering sep1 :
  (Monad m, Catchable m e, Sequence s i, ParseError e, Semigroup e) =>
  Parser m e s i a ->
  Parser m e s i b ->
  Parser m e s i (List b)
sep1 p q = rethrowStr "sep1: " [| q :: many (p *> q) |]

covering sepBy1 :
  (Monad m, Catchable m e, Sequence s i, ParseError e, Semigroup e) =>
  Parser m e s i a ->
  Parser m e s i b ->
  Parser m e s i (List a)
sepBy1 p q = rethrowStr "sepBy1: " (sep1 q p)

between :
  (Monad m, Catchable m e, Sequence s i, ParseError e, Semigroup e) =>
  Parser m e s i a ->
  Parser m e s i b ->
  Parser m e s i c ->
  Parser m e s i c
between p r q = rethrowStr "between: " (p *> q <* r)

covering spaces : (Monad m, Catchable m e, Sequence s Char, ParseError e) => Parser m e s Char (List Char)
spaces = many (match isSpace)

covering spaces1 : (Monad m, Catchable m e, Sequence s Char, ParseError e, Semigroup e) => Parser m e s Char (List Char)
spaces1 = many1 (match isSpace) <|> throwStr "spaces1 failed"

StringParser : (Type -> Type) -> Type -> Type
StringParser m = Parser m String String Char
