module Parser

import Data.Vect

%access public

%default partial

-- resolution only works if I specify that it's not dependent on e - why?
class Sequence s e | s where
  cons : e -> s -> s
  uncons : s -> Maybe (e, s)

instance Sequence (List a) a where
  cons = (::)
  uncons [] = Nothing
  uncons (x :: xs) = Just (x, xs)

instance Sequence String Char where
  cons = strCons
  uncons "" = Nothing
  uncons str = Just (assert_total (strHead str), assert_total (strTail str))


%default total

data Result : Type -> Type -> Type where
  MkResult : o -> s -> Result s o

instance Show o => Show (Result s o) where
  show (MkResult x _) = show x

instance Functor (Result i) where
  map f (MkResult x sf) = MkResult (f x) sf

output : Result i o -> o
output (MkResult x _) = x

data Parser : Type -> Type -> Type -> Type -> Type where
  MkParser : Sequence s i => (s -> Either e (Result s o)) -> Parser e s i o

class ParseError e where
  fromString : String -> e

instance ParseError String where
  fromString = id

runParser : Parser e s i o -> s -> Either e (Result s o)
runParser (MkParser f) = f

execParser : Parser e s i o -> s -> Either e o
execParser f xs = map output (runParser f xs)

instance (Sequence s i, Semigroup o) => Semigroup (Parser e s i o) where
  p <+> q = MkParser $ \i => do
    MkResult op i' <- runParser p i
    MkResult oq i'' <- runParser q i'
    return (MkResult (op <+> oq) i'')

instance (Sequence s i, Monoid o) => Monoid (Parser e s i o) where
  neutral = MkParser $ \i => Right (MkResult neutral i)

instance Sequence s i => Functor (Parser e s i) where
  map f (MkParser g) = MkParser $ \i => map f <$> g i

instance Sequence s i => Applicative (Parser e s i) where
  pure x = MkParser $ \i => Right (MkResult x i)

  p <*> q = MkParser $ \i => do
    MkResult op i' <- runParser p i
    MkResult oq i'' <- runParser q i'
    return (MkResult (op oq) i'')

failWith : Sequence s i => e -> Parser e s i o
failWith err = MkParser (const (Left err))

private throw : (Sequence s i, ParseError e) => String -> Parser e s i o
throw = failWith . fromString

instance (Sequence s i, ParseError e) => Alternative (Parser e s i) where
  empty = throw "empty"
  f <|> g = MkParser $ \i =>
    case runParser f i of
      Left err => runParser g i
      Right result => return result

choice : (Sequence s i, ParseError e) => Vect (S n) (Parser e s i o) -> Parser e s i o
choice ps = foldl1 (<|>) ps

instance Sequence s i => Monad (Parser e s i) where
  g >>= f = MkParser $ \i => do
    MkResult o i' <- runParser g i
    MkResult o' i'' <- runParser (f o) i'
    return (MkResult o' i'')

noop : (Sequence s i, Monoid o) => Parser e s i o
noop = neutral

maybe : (Sequence s i, ParseError e) => Parser e s i o -> Parser e s i (Maybe o)
maybe p = MkParser $ \i =>
  case runParser p i of
    Right (MkResult o i') => Right (MkResult (Just o) i')
    Left _ => Right (MkResult Nothing i)

matchMap : (Sequence s i, ParseError e) => (i -> Maybe o) -> Parser e s i o
matchMap f = MkParser $ \i => 
  case uncons i of
    Nothing => Left (fromString "matchMap failed: no input")
    Just (x, xs) =>
      case f x of
        Nothing => Left (fromString "matchMap failed: bad input")
        Just x => Right (MkResult x xs)

match : (Sequence s i, ParseError e) => (i -> Bool) -> Parser e s i i
match f = matchMap (\x => if f x then Just x else Nothing) <|> throw "match failed"

token : (Sequence s i, ParseError e, Eq i) => i -> Parser e s i i
token x = match (== x) <|> throw "token failed"

covering string : (Sequence s i, Monoid s, ParseError e, Eq i) => s -> Parser e s i s
string s =
  case uncons s of
    Nothing => noop
    Just (x, xs) => [| cons (token x) (string xs) |] <|> throw "string failed"

ignore : Sequence s i => Parser e s i o -> Parser e s i ()
ignore = map (const ())

covering many : (Sequence s i, ParseError e) => Parser e s i o -> Parser e s i (List o)
many p = do
  x <- maybe p
  case x of
    Nothing => return []
    Just x' => return (x' :: !(many p))

covering many' : (Sequence s i, ParseError e) => Parser e s i o -> Parser e s i ()
many' p = do
  x <- maybe p
  case x of
    Nothing => return ()
    Just _ => many' p

guard : (Sequence s i, ParseError e) => (o -> Bool) -> Parser e s i o -> Parser e s i o
guard f p = do
  x <- p
  if f x then return x else throw "guard failed"

iff : (Sequence s i, ParseError e) => Parser e s i o -> (o -> Bool) -> Parser e s i o
iff = flip guard

covering many1 : (Sequence s i, ParseError e) => Parser e s i i -> Parser e s i (List i)
many1 p = guard (isSucc . length) (many p) <|> throw "many1 failed"

covering sep1 :
  (Sequence s i, ParseError e) =>
  Parser e s i a ->
  Parser e s i b ->
  Parser e s i (List b)
sep1 p q = [| q :: many (p *> q) |] <|> throw "sep1 failed"

covering sepBy1 :
  (Sequence s i, ParseError e) =>
  Parser e s i a ->
  Parser e s i b ->
  Parser e s i (List a)
sepBy1 p q = sep1 q p <|> throw "sepBy1 failed"

between :
  (Sequence s i, ParseError e) =>
  Parser e s i a ->
  Parser e s i b ->
  Parser e s i c ->
  Parser e s i c
between p r q = (p *> q <* r) <|> throw "between failed"

covering spaces : (Sequence s Char, ParseError e) => Parser e s Char (List Char)
spaces = many (match isSpace)

covering spaces1 : (Sequence s Char, ParseError e) => Parser e s Char (List Char)
spaces1 = many1 (match isSpace) <|> throw "spaces1 failed"

StringParser : Type -> Type
StringParser = Parser String String Char
