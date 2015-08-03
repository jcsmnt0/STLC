module Parser

%default total

data Parser : Type -> Type -> Type where
  MkParser : (List i -> Maybe (o, List i)) -> Parser i o

StringParser : Type -> Type
StringParser = Parser Char

runParser : Parser i o -> List i -> Maybe (o, List i)
runParser (MkParser f) = f

execParser : Parser i o -> List i -> Maybe o
execParser f = map fst . runParser f

instance Semigroup a => Semigroup (Parser i a) where
  p <+> q = MkParser $ \i => do
    (op, i') <- runParser p i
    (oq, i'') <- runParser q i'
    return (op <+> oq, i'')

instance Monoid a => Monoid (Parser i a) where
  neutral = MkParser $ \i => Just (neutral, i)

instance Functor (Parser i) where
  map f (MkParser g) = MkParser $ \i => do
    (o, i') <- g i
    return (f o, i')

instance Applicative (Parser i) where
  pure x = MkParser $ \i => Just (x, i)

  f <*> g = MkParser $ \i => do
    (f', i') <- runParser f i
    (o, i'') <- runParser g i'
    return (f' o, i'')

instance Alternative (Parser i) where
  empty = MkParser $ \_ => Nothing

  f <|> g = MkParser $ \i => runParser f i <|> runParser g i

instance Monad (Parser i) where
  g >>= f = MkParser $ \i => do
    (o, i') <- runParser g i
    runParser (f o) i'

fail : Parser a b
fail = empty

noop : Monoid b => Parser a b
noop = neutral

maybe : Parser a b -> Parser a (Maybe b)
maybe p = MkParser $ \i =>
  case runParser p i of
    Just (o, i') => Just (Just o, i')
    Nothing => Just (Nothing, i)

matchMap : (a -> Maybe b) -> Parser a b
matchMap f = MkParser matchMap'
  where
    matchMap' : List a -> Maybe (b, List a)
    matchMap' [] = Nothing
    matchMap' (x :: xs) = return $ (!(f x), xs)

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

-- hmm
many : Parser a b -> Parser a (List b)
many p = MkParser $ \i =>
  case runParser p i of
    Nothing => Just ([], i)
    Just (x, i') =>
      -- total as long as i' is always smaller than i
      case assert_total (runParser (many p) i') of
        Just (xs, i'') => Just (x :: xs, i'')
        Nothing => Nothing

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

-- namespace test
--   p0 : Parser Nat Nat
--   p0 = (many (exactly 5) $> exactly 2) <|> (exactly 5 $> exactly 3)
-- 
--   p0t0 : runParser p0 [5, 5, 5, 2] = Just (2, [])
--   p0t0 = Refl
-- 
--   p0t1 : runParser p0 [5, 3] = Just (3, [])
--   p0t1 = Refl
