module ParseSyntax

import Parser
import PiVect
import Ty

import Util.Vect

%default total

namespace RawSyn
  ||| Raw syntax, without any depth or scope or type information.
  ||| Only really exists because it's a hassle to write parsers that return (d : Nat ** Syn d) and do all the
  ||| lifting inside the parser code, so instead these parsing functions return RawSyns that can be converted to
  ||| depth-tagged Syns afterward.
  data RawSyn
    = Var String
    | Num Float
    | Bool Bool
    | Lam String Ty RawSyn
    | (:$) RawSyn RawSyn
    | If RawSyn RawSyn RawSyn
    | Tuple (Vect n RawSyn)

data SynParseError
  = ParseError ParseError
  | TyError String
  | IdentError String

instance Show SynParseError where
  show (ParseError p) = show p
  show (TyError ty) = ty ++ " is not a valid type"
  show (IdentError ident) = ident ++ " is not a valid identifier"

instance Cast ParseError SynParseError where
  cast = ParseError

SynParser : Type
SynParser = StringParser SynParseError RawSyn

isLowercaseLetter : Char -> Bool
isLowercaseLetter c = 'a' <= c && c <= 'z'

isUppercaseLetter : Char -> Bool
isUppercaseLetter c = 'A' <= c && c <= 'Z'

isIdentChar : Char -> Bool
isIdentChar c =
  isLowercaseLetter c ||
  isUppercaseLetter c ||
  (elem c (unpack "+=<>_!@#$%^&*-|'\"?/`~"))

keywords : List String
keywords =
  [ "if"
  , "then"
  , "else"
  , "def"
  ]

{- It seems like there's no hope of getting these parsers to pass the totality checker - at least not without
   a different implementation of the Parser monad, but I'm not sure what that implementation would look like or
   whether it even exists in theory. -}
%default partial

parseIdent : StringParser SynParseError String
parseIdent = pack <$> guard isValid (many1 (match isIdentChar <|> match isDigit))
  where
    isValid : List Char -> Bool
    isValid [] = False -- can't happen because of many1
    isValid (x :: _) = not (isDigit x)

parseTy : StringParser SynParseError Ty
parseTy = parseFunTy <|> parseParens <|> parseBaseTy
  where
    parseBaseTy : StringParser SynParseError Ty
    parseBaseTy = do
      ty <- many (match isLowercaseLetter <|> match isUppercaseLetter)
      case pack ty of
        "Num" => return Num
        "Bool" => return Bool
        ty' => failWith (TyError ty')

    parseParens : StringParser SynParseError Ty
    parseParens = do
      exactly '(' *> spaces
      parseTupleTy <|> parseSumTy <|> (parseTy <* spaces <* exactly ')')
    where
      parseTupleTy : StringParser SynParseError Ty
      parseTupleTy = do
        tys <- sep1 (exactly ',' *> spaces) parseTy <* spaces <* exactly ')'
        let (_ ** tys') = toVect tys
        return (Tuple tys')

      parseSumTy : StringParser SynParseError Ty
      parseSumTy = do
        tys <- sep1 (spaces *> exactly '|' <* spaces) parseTy <* spaces <* exactly ')'
        let (_ ** tys') = toVect tys
        return (Sum tys')

    parseFunTy : StringParser SynParseError Ty
    parseFunTy = do
      a <- parseBaseTy <|> parseParens
      let separator = spaces *> roughly "->" *> spaces
      as <- separator *> sep1 separator parseTy
      return (foldr (:->) a as)

parseSyn : SynParser
parseSyn = parseApp <|> parseParens <|> parseLam <|> parseNat <|> parseKeyword <|> parseVar
  where
    parseVar : SynParser
    parseVar = Var <$> guard (\ident => not (elem ident keywords)) parseIdent

    parseKeyword : SynParser
    parseKeyword =
      case !parseIdent of
        "true" => return (Bool True)
        "false" => return (Bool False)
        "if" => do
          spaces
          body <- parseSyn
          spaces1 *> roughly "then" *> spaces1
          t <- parseSyn
          spaces1 *> roughly "else" *> spaces1
          f <- parseSyn
          return (If body t f)
        ident => failWith (IdentError ident)

    parseNat : SynParser
    parseNat = do
      xs <- many1 (match isDigit)
      return (Num (cast {to = Float} (pack xs)))

    parseLam : SynParser
    parseLam = do
      exactly '\\' *> spaces
      var <- parseIdent
      spaces *> exactly ':' *> spaces
      ty <- parseTy
      exactly '.' *> spaces
      expr <- parseSyn
      return (Lam var ty expr)

    parseParens : SynParser
    parseParens = do
      exactly '(' *> spaces
      expr <- parseSyn
      parseTuple expr <|> parseEndParen expr
    where
      parseEndParen : RawSyn -> SynParser
      parseEndParen expr = do
        spaces *> exactly ')'
        return expr

      parseTuple : RawSyn -> SynParser
      parseTuple x = do
        let separator = spaces *> exactly ',' *> spaces
        (_ ** xs) <- toVect <$> (separator *> sep1 separator parseSyn)
        exactly ')'
        return (Tuple (x :: xs))

    parseApp : SynParser
    parseApp = do
      x <- parseParens <|> parseLam <|> parseNat <|> parseKeyword <|> parseVar
      xs <- spaces1 *> sep1 spaces1 (parseParens <|> parseLam <|> parseNat <|> parseKeyword <|> parseVar)
      return (foldl (:$) x xs)
