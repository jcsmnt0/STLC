module ParseSyntax

import Parser
import PiVect
import Syntax
import Ty

import Util.Dec
import Util.LTE
import Util.Vect

%default total

namespace RawSyn
  ||| Raw syntax, without any depth or scope or type information.
  data RawSyn
    = Var String
    | Num Float
    | Bool Bool
    | Lam String Ty RawSyn
    | (:$) RawSyn RawSyn
    | If RawSyn RawSyn RawSyn
    | Tuple (Vect n RawSyn)

  tagDepth :
    RawSyn ->
    (d ** Syn d)

  tagDepth (Var v) =
    (Z ** Var v)

  tagDepth (Num x) =
    (Z ** Num x)

  tagDepth (Bool x) =
    (Z ** Bool x)

  tagDepth (Lam v ty r) =
    let (d ** s) = tagDepth r in
      (S d ** Lam v ty s)

  tagDepth (rx :$ ry) =
    let (dx ** sx) = tagDepth rx in
    let (dy ** sy) = tagDepth ry in
    let (d ** [px, py]) = upperBound [dx, dy] in
      (S d ** lift px sx :$ lift py sy)

  tagDepth (If rb rt rf) =
    let (db ** sb) = tagDepth rb in
    let (dt ** st) = tagDepth rt in
    let (df ** sf) = tagDepth rf in
    let (d ** [pb, pt, pf]) = upperBound [db, dt, df] in
      (S d ** If (lift pb sb) (lift pt st) (lift pf sf))

  {- assert_total is necessary here because RawSyn isn't tagged with depth information, so there's no argument to
     tagDepth that decreases in size in the expression "map tagDepth" that the totality checker can latch
     onto. It should be impossible to construct an infinite RawSyn because it should be impossible to input an
     infinite amount of source code, so this won't ever fail to terminate. -}
  tagDepth (Tuple rs) =
    let (ds ** ss) = unzipToPiVect (map (assert_total tagDepth) rs) in
    let (d ** ps) = upperBound ds in
      (S d ** Tuple (zipWithIdToVect (lift {n = d}) ps ss))

-- it should probably be possible to have the parsers return things of type (d ** Syn d)
-- in order to get around the issue of depth tagging not being structurally recursive
SynParser : Type
SynParser = StringParser RawSyn

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
   a different implementation of the Parser monad, but I'm not sure what that implementation would look like. -}
%default partial

parseIdent : StringParser String
parseIdent = pack <$> guard isValid (many1 (match isIdentChar <|> match isDigit))
  where
    isValid : List Char -> Bool
    isValid [] = False -- can't happen because of many1
    isValid (x :: _) = not (isDigit x)

parseTy : StringParser Ty
parseTy = parseFunTy <|> parseParens <|> parseBaseTy
  where
    parseBaseTy : StringParser Ty
    parseBaseTy = do
      ty <- many (match isLowercaseLetter <|> match isUppercaseLetter)
      case pack ty of
        "Num" => return Num
        "Bool" => return Bool
        _ => fail

    parseParens : StringParser Ty
    parseParens = do
      exactly '(' *> spaces
      parseTupleTy <|> (parseTy <* spaces <* exactly ')')
    where
      parseTupleTy : StringParser Ty
      parseTupleTy = do
        tys <- sep1 (exactly ',' *> spaces) parseTy <* spaces <* exactly ')'
        let (_ ** tys') = toVect tys
        return (Tuple tys')

    parseFunTy : StringParser Ty
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
        _ => fail

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
