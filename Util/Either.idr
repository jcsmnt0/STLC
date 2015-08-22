module Either

(<|>) : Either a b -> Either a b -> Either a b
(Right x) <|> _ = Right x
(Left _) <|> y = y

mapLeft : (a -> b) -> Either a c -> Either b c
mapLeft f (Left x) = Left (f x)
mapLeft _ (Right y) = Right y
