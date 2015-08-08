module Parser

%default total

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

data Parser : Type -> Type -> Type where
  MkParser : ((xs : List i) -> Maybe (Result xs i o)) -> Parser i o

StringParser : Type -> Type
StringParser = Parser Char

runParser : Parser i o -> (xs : List i) -> Maybe (Result xs i o)
runParser (MkParser f) = f

execParser : Parser i o -> List i -> Maybe o
execParser f xs = map output (runParser f xs)

instance Semigroup a => Semigroup (Parser i a) where
  p <+> q = MkParser $ \i => do
    MkResult op i' sfp <- runParser p i
    MkResult oq i'' sfq <- runParser q i'
    return (MkResult (op <+> oq) i'' (sfp ++ sfq))

instance Monoid a => Monoid (Parser i a) where
  neutral = MkParser $ \i => Just (MkResult neutral i [])

instance Functor (Parser i) where
  map f (MkParser g) = MkParser $ \i => map f <$> g i

instance Applicative (Parser i) where
  pure x = MkParser $ \i => Just (MkResult x i [])

  p <*> q = MkParser $ \i => do
    MkResult op i' sfp <- runParser p i
    MkResult oq i'' sfq <- runParser q i'
    return (MkResult (op oq) i'' (sfp ++ sfq))

instance Alternative (Parser i) where
  empty = MkParser $ \_ => Nothing

  f <|> g = MkParser $ \i => runParser f i <|> runParser g i

instance Monad (Parser i) where
  g >>= f = MkParser $ \i => do
    MkResult o i' sf <- runParser g i
    MkResult o' i'' sf' <- runParser (f o) i'
    return (MkResult o' i'' (sf ++ sf'))

fail : Parser a b
fail = empty

noop : Monoid b => Parser a b
noop = neutral

maybe : Parser a b -> Parser a (Maybe b)
maybe p = MkParser $ \i =>
  case runParser p i of
    Just (MkResult o i' sf) => Just (MkResult (Just o) i' sf)
    Nothing => Just (MkResult Nothing i [])

matchMap : (a -> Maybe b) -> Parser a b
matchMap f = MkParser matchMap'
  where
    matchMap' : (xs : List a) -> Maybe (Result xs a b)
    matchMap' [] = Nothing
    matchMap' (x :: xs) = return $ (MkResult !(f x) xs [x])

match : (a -> Bool) -> Parser a a
match f = matchMap (\x => if f x then Just x else Nothing)

exactly : Eq a => a -> Parser a a
exactly x = match (== x)
 
exactlyList : Eq a => List a -> Parser a (List a)
exactlyList [] = noop
exactlyList (x :: xs) = [| exactly x :: exactlyList xs |]

roughly : (Cast a (List b), Eq b) => a -> Parser b (List b)
roughly = exactlyList . cast

ignore : Parser a b -> Parser a ()
ignore = map (const ())

many : Parser a b -> Parser a (List b)
many p = do
  x <- maybe p
  case x of
    Nothing => return []
    Just x' => return (x' :: !(assert_total (many p)))

guard : (b -> Bool) -> Parser a b -> Parser a b
guard f p = do
  x <- p
  if f x then return x else fail

iff : Parser a b -> (b -> Bool) -> Parser a b
iff = flip guard

many1 : Parser a a -> Parser a (List a)
many1 = guard (isSucc . length) . many

spaces : StringParser (List Char)
spaces = many (match isSpace)

spaces1 : StringParser (List Char)
spaces1 = many1 (match isSpace)

sep1 : Parser a c -> Parser a b -> Parser a (List b)
sep1 p q = [| q :: many (p *> q) |]

sepBy1 : Parser a b -> Parser a c -> Parser a (List b)
sepBy1 = flip sep1

between : Parser a c -> Parser a d -> Parser a b -> Parser a b
between p r q = p *> q <* r
