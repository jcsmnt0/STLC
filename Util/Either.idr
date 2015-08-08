module Either

(<|>) : Either a b -> Either a b -> Either a b
(Right x) <|> _ = Right x
(Left _) <|> y = y
