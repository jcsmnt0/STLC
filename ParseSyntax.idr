module ParseSyntax

import Control.Catchable
import Data.Vect

import Parser
import PVect
import Syntax
import Ty

import Util.Ex
import Util.LTE
import Util.Sigma
import Util.Vect

%default total

SynParser : (Type -> Type) -> Type
SynParser m = StringParser m (Ex Syn)

TyParser : (Type -> Type) -> Type
TyParser m = StringParser m Ty

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
  , "fn"
  , "let"
  , "in"
  , "case"
  , "of"
  , "variant"
  , "def"
  ]

liftSyn : (m `LTE` n) -> Syn m -> Syn n
liftSyn p (Var v) = Var v
liftSyn p (Num x) = Num x
liftSyn p (Bool x) = Bool x
liftSyn p (As s a) = As (liftSyn p s) a
liftSyn p (sx :$ sy) = liftSyn p sx :$ liftSyn p sy
liftSyn (LTESucc p) (Let v s t) = Let v (liftSyn (LTESucc p) s) (liftSyn p t)
liftSyn (LTESucc p) (LamRec vf a v b s) = LamRec vf a v b (liftSyn p s)
liftSyn (LTESucc p) (Lam v ty s) = Lam v ty (liftSyn p s)
liftSyn (LTESucc p) (If sb st sf) = If (liftSyn p sb) (liftSyn p st) (liftSyn p sf)
liftSyn (LTESucc p) (Tuple ss) = Tuple (map (liftSyn p) ss)
liftSyn (LTESucc p) (Variant ety s) = Variant ety (liftSyn p s)
-- m is definitely decreasing in the recursive call here, I'm not sure why it's not picked up as total
liftSyn (LTESucc p) (Case s ss) = Case (liftSyn p s) (map (\(v, s) => (v, assert_total (liftSyn p s))) ss)
liftSyn (LTESucc p) (Unpack vs s t) = Unpack vs (liftSyn (LTESucc p) s) (liftSyn p t)

liftSyns : {ds : Vect n Nat} -> (ss : PVect Syn ds) -> Vect n (Syn (fst (upperBound ds)))
liftSyns {ds = ds} ss = zipWithToVect liftSyn (snd (upperBound ds)) ss

liftExSyns : (ss : Vect n (Ex Syn)) -> Vect n (Syn (fst (upperBound (map fst ss))))
liftExSyns ss = liftSyns (unzip ss)

E0 : b Z -> Ex b
E0 = E


%default partial

covering parseIdent : (Monad m, Catchable m String) => StringParser m String
parseIdent = pack <$> guard isValid (many1 (match isIdentChar <|> match isDigit))
  where
    isValid : List Char -> Bool
    isValid [] = False -- can't happen because of many1
    isValid (x :: _) = not (isDigit x)

covering parseTy : (Monad m, Catchable m String) => TyParser m
parseTy = parseLamRecTy <|> parseParenTy <|> parseBaseTy
  where
    parseBaseTy : (Monad m, Catchable m String) => TyParser m
    parseBaseTy = do
      ty <- many (match isLowercaseLetter <|> match isUppercaseLetter)
      case pack ty of
        "Num" => return Num
        "Bool" => return Bool
        ty' => failWith (pack ty ++ " isn't a valid type")

    parseParenTy : (Monad m, Catchable m String) => TyParser m
    parseParenTy = do
      token '(' *> spaces
      parseTupleTy <|> parseSumTy <|> (parseTy <* spaces <* token ')')
    where
      parseTupleTy : (Monad m, Catchable m String) => TyParser m
      parseTupleTy = do
        xs <- sep1 (spaces *> token ',' *> spaces) parseTy <* spaces <* token ')'
        return (Tuple (toVect xs))

      parseSumTy : (Monad m, Catchable m String) => TyParser m
      parseSumTy = do
        xs <- sep1 (spaces *> token '|' *> spaces) parseTy <* spaces <* token ')'
        return (Sum (toVect xs))

    parseLamRecTy : (Monad m, Catchable m String) => TyParser m
    parseLamRecTy = do
      a <- parseBaseTy <|> parseParenTy
      let separator = spaces *> string "->" *> spaces
      as <- separator *> sep1 separator parseTy
      return (foldl (:->) a as)

covering parseNat : (Monad m, Catchable m String) => StringParser m Nat
parseNat = do
  xs <- many1 (match isDigit)
  return (cast {to = Nat} $ cast {to = Int} $ pack xs)

covering parseFloat : (Monad m, Catchable m String) => StringParser m Float
parseFloat = do
  xs <- many1 (match isDigit)
  return (cast {to = Float} $ pack xs)

mutual
  covering parseSyn : (Monad m, Catchable m String) => SynParser m
  parseSyn = do
    s <- parseAs <|>
      parseVariant <|>
      parseParenSyn <|>
      parseLamRec <|>
      parseLet <|>
      parseLam <|>
      parseNum <|>
      parseBool <|>
      parseIf <|>
      parseCase <|>
      parseVar <|>
      failWith "couldn't parse"
    parseApp s

  covering parseApp : (Monad m, Catchable m String) => Ex Syn -> SynParser m
  parseApp f = do
    arg <- maybe (spaces1 *> (parseParenSyn <|> parseBool <|> parseNum <|> parseVar))
    case arg of
      Nothing => return f
      Just x => let [f', x'] = liftExSyns [f, x] in parseApp (E (f' :$ x'))

  covering parseVar : (Monad m, Catchable m String) => SynParser m
  parseVar = E0 . Var <$> guard (\ident => not (elem ident keywords)) parseIdent

  covering parseBool : (Monad m, Catchable m String) => SynParser m
  parseBool =
    case !parseIdent of
      "true" => return (E0 $ Bool True)
      "false" => return (E0 $ Bool False)
      ident => failWith (ident ++ " isn't a bool literal")

  covering parseIf : (Monad m, Catchable m String) => SynParser m
  parseIf = do
    string "if" *> spaces1
    b <- parseSyn
    spaces1 *> string "then" *> spaces1
    t <- parseSyn
    spaces1 *> string "else" *> spaces1
    f <- parseSyn
    let [b', t', f'] = liftExSyns [b, t, f]
    return (E $ If b' t' f')

  covering parseAs : (Monad m, Catchable m String) => SynParser m
  parseAs = do
    E t <- parseVariant <|>
      parseParenSyn <|>
      parseLam <|>
      parseLamRec <|>
      parseLet <|>
      parseNum <|>
      parseBool <|>
      parseIf <|>
      parseCase <|>
      parseVar
    spaces *> token ':' *> spaces
    ty <- parseTy
    return (E $ t `As` ty)

  covering parseNum : (Monad m, Catchable m String) => SynParser m
  parseNum = do
    x <- parseFloat
    return (E0 $ Num x)

  covering parseLam : (Monad m, Catchable m String) => SynParser m
  parseLam = do
    token '\\' *> spaces
    var <- parseIdent
    spaces *> token ':' *> spaces
    ty <- parseTy
    token '.' *> spaces
    E expr <- parseSyn
    return (E $ Lam var ty expr)

  covering parseLamRec : (Monad m, Catchable m String) => SynParser m
  parseLamRec = do
    string "fn" *> spaces1
    vf <- parseIdent
    spaces *> token '(' *> spaces
    v <- parseIdent
    spaces *> token ':' *> spaces
    a <- parseTy
    spaces *> token ')'
    spaces *> token ':' *> spaces
    b <- parseTy
    token '.' *> spaces
    E expr <- parseSyn
    return (E $ LamRec vf a v b expr)

  covering parseLet : (Monad m, Catchable m String) => SynParser m
  parseLet = do
    string "let" *> spaces
    parseUnpackingLet <|> parseSimpleLet
  where
    parseUnpackingLet : (Monad m, Catchable m String) => SynParser m
    parseUnpackingLet = do
      vs <- between (token '(') (token ')') (sep1 (spaces *> token ',' *> spaces) parseIdent)
      spaces *> token '=' *> spaces
      E s <- parseSyn
      spaces1 *> string "in" *> spaces1
      E t <- parseSyn
      let [s', t'] = liftSyns [s, t]
      return (E $ Unpack (toVect vs) (liftSyn lteSucc s') t')

    parseSimpleLet : (Monad m, Catchable m String) => SynParser m
    parseSimpleLet = do
      v <- parseIdent
      spaces *> token '=' *> spaces
      E s <- parseSyn
      spaces1 *> string "in" *> spaces1
      E t <- parseSyn
      let [s', t'] = liftSyns [s, t]
      return (E $ Let v (liftSyn lteSucc s') t')

  covering parseCase : (Monad m, Catchable m String) => SynParser m
  parseCase = do
    string "case" *> spaces1
    s <- parseSyn
    spaces1 *> string "of" *> spaces1
    token '{' *> spaces
    let separator = spaces *> token ';' *> spaces
    cases <- sep1 separator [| MkPair (parseIdent <* spaces1 <* string "=>" <* spaces1) parseSyn |]
    maybe separator
    let (vs, ss) = unzip (toVect cases)
    let (s' :: ss') = liftExSyns (s :: ss)
    spaces *> token '}'
    return (E $ Case s' (zip vs ss'))

  covering parseVariant : (Monad m, Catchable m String) => SynParser m
  parseVariant = do
    string "variant" *> spaces1
    i <- parseNat
    spaces1
    E s <- parseVariant <|>
      parseParenSyn <|>
      parseLamRec <|>
      parseLet <|>
      parseLam <|>
      parseNum <|>
      parseBool <|>
      parseIf <|>
      parseCase <|>
      parseVar
    return (E $ Variant i s)

  covering parseParenSyn : (Monad m, Catchable m String) => SynParser m
  parseParenSyn = do
    token '(' *> spaces
    expr <- parseSyn
    parseTuple expr <|> parseEndParen expr
  where
    parseEndParen : (Monad m, Catchable m String) => Ex Syn -> SynParser m
    parseEndParen expr = do
      spaces *> token ')'
      return expr

    parseTuple : (Monad m, Catchable m String) => Ex Syn -> SynParser m
    parseTuple x = do
      let separator = spaces *> token ',' *> spaces
      xs <- separator *> sep1 separator parseSyn
      token ')'
      return (E $ Tuple (liftExSyns (x :: toVect xs)))

covering parseDef : (Monad m, Catchable m String) => StringParser m (String, Ex Syn)
parseDef = do
  string "def" *> spaces1
  name <- parseIdent
  spaces1 *> token '=' *> spaces1
  s <- parseSyn
  return (name, s)
