module Parser

import Util.Either

%default total
%access public

data Suffix : List a -> List a -> Type where
  Nil : Suffix xs xs
  (::) : (x : a) -> Suffix ys xs -> Suffix ys (x :: xs)

(++) : Suffix ys xs -> Suffix zs ys -> Suffix zs xs
(++) [] sf' = sf'
(++) (x :: sf) sf' = x :: (sf ++ sf')

data Result : List a -> Type -> Type -> Type where
  MkResult : o -> (ys : List i) -> Suffix ys xs -> Result xs i o

instance Functor (Result xs i) where
  map f (MkResult x ys sf) = MkResult (f x) ys sf

output : Result xs i o -> o
output (MkResult x _ _) = x

data Parser : Type -> Type -> Type -> Type where
  MkParser : ((xs : List i) -> Either e (Result xs i o)) -> Parser e i o

record ParseError where
  constructor Err
  message : String

instance Show ParseError where
  show = message

runParser : Parser e i o -> (xs : List i) -> Either e (Result xs i o)
runParser (MkParser f) = f

execParser : Parser e i o -> List i -> Either e o
execParser f xs = map output (runParser f xs)

instance Semigroup o => Semigroup (Parser e i o) where
  p <+> q = MkParser $ \i => do
    MkResult op i' sfp <- runParser p i
    MkResult oq i'' sfq <- runParser q i'
    return (MkResult (op <+> oq) i'' (sfp ++ sfq))

instance Monoid o => Monoid (Parser e i o) where
  neutral = MkParser $ \i => Right (MkResult neutral i [])

instance Functor (Parser e i) where
  map f (MkParser g) = MkParser $ \i => map f <$> g i

instance Applicative (Parser e i) where
  pure x = MkParser $ \i => Right (MkResult x i [])

  p <*> q = MkParser $ \i => do
    MkResult op i' sfp <- runParser p i
    MkResult oq i'' sfq <- runParser q i'
    return (MkResult (op oq) i'' (sfp ++ sfq))

(<|>) : Parser e i o -> Parser e i o -> Parser e i o
f <|> g = MkParser $ \i => runParser f i <|> runParser g i

instance Monad (Parser e i) where
  g >>= f = MkParser $ \i => do
    MkResult o i' sf <- runParser g i
    MkResult o' i'' sf' <- runParser (f o) i'
    return (MkResult o' i'' (sf ++ sf'))

failWith : e -> Parser e i o
failWith err = MkParser $ \_ => Left err

private err : Cast ParseError e => String -> e
err = cast . Err

private throw : Cast ParseError e => String -> Parser e i o
throw = failWith . err

noop : Monoid o => Parser e i o
noop = neutral

maybe : Parser e i o -> Parser e i (Maybe o)
maybe p = MkParser $ \i =>
  case runParser p i of
    Right (MkResult o i' sf) => Right (MkResult (Just o) i' sf)
    Left _ => Right (MkResult Nothing i [])

matchMap : Cast ParseError e => (i -> Maybe o) -> Parser e i o
matchMap f = MkParser $ \i =>
  case i of
    [] => Left (err "matchMap failed: no input")
    (x :: xs) =>
      case f x of
        Nothing => Left (err "matchMap failed: bad input")
        Just x' => Right (MkResult x' xs [x])

match : Cast ParseError e => (i -> Bool) -> Parser e i i
match f = matchMap (\x => if f x then Just x else Nothing) <|> throw "match failed"

exactly : (Cast ParseError e, Eq i) => i -> Parser e i i
exactly x = match (== x) <|> failWith (err "exactly failed")

exactlyList : (Cast ParseError e, Eq i) => List i -> Parser e i (List i)
exactlyList [] = noop
exactlyList (x :: xs) = [| exactly x :: exactlyList xs |] <|> throw "exactlyList failed"

roughly : (Cast ParseError e, Cast a (List i), Eq i) => a -> Parser e i (List i)
roughly = exactlyList . cast

ignore : Parser e i o -> Parser e i ()
ignore = map (const ())

partial many : Parser e i o -> Parser e i (List o)
many p = do
  x <- maybe p
  case x of
    Nothing => return []
    Just x' => return (x' :: !(many p))

guard : Cast ParseError e => (o -> Bool) -> Parser e i o -> Parser e i o
guard f p = do
  x <- p
  if f x then return x else throw "guard failed"

iff : Cast ParseError e => Parser e i o -> (o -> Bool) -> Parser e i o
iff = flip guard

partial many1 : Cast ParseError e => Parser e i i -> Parser e i (List i)
many1 = guard (isSucc . length) . many

partial sep1 : Parser e i a -> Parser e i b -> Parser e i (List b)
sep1 p q = [| q :: many (p *> q) |]

partial sepBy1 : Parser e i a -> Parser e i b -> Parser e i (List a)
sepBy1 = flip sep1

between : Parser e i a -> Parser e i b -> Parser e i c -> Parser e i c
between p r q = p *> q <* r

StringParser : Type -> Type -> Type
StringParser e = Parser e Char

partial spaces : Cast ParseError e => StringParser e (List Char)
spaces = many (match isSpace)

partial spaces1 : Cast ParseError e => StringParser e (List Char)
spaces1 = many1 (match isSpace)
