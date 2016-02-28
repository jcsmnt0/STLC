module ParseTermtax

import Control.Catchable
import Data.Vect
import Data.Vect.Quantifiers

import Term.Raw
import Ty.Raw

import Parser
import Util.All
import Util.Ex
import Util.LTE
import Util.Sigma
import Util.Vect

%default total

TermParser : (Type -> Type) -> Type
TermParser m = StringParser m (Ex Term)

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

liftTerm : (m `LTE` n) -> Term m -> Term n
liftTerm p (Var v) = Var v
liftTerm p (Num x) = Num x
liftTerm (LTESucc (LTESucc p)) (Bool x) = Bool x
liftTerm p (As s a) = As (liftTerm p s) a
liftTerm (LTESucc p) (sx :$ sy) = liftTerm p sx :$ liftTerm p sy
liftTerm (LTESucc (LTESucc p)) (Let v s t) = Let v (liftTerm (LTESucc p) s) (liftTerm p t)
liftTerm (LTESucc p) (LamRec vf a v b s) = LamRec vf a v b (liftTerm p s)
liftTerm (LTESucc p) (Lam v ty s) = Lam v ty (liftTerm p s)
liftTerm (LTESucc p) (Tuple ss) = Tuple (map (liftTerm p) ss)
liftTerm (LTESucc p) (Variant ety s) = Variant ety (liftTerm p s)
liftTerm (LTESucc p) (Unpack vs s t) = Unpack vs (liftTerm p s) (liftTerm p t)
liftTerm (LTESucc (LTESucc (LTESucc p))) (Case s ss) = Case (liftTerm p s) (map (liftTerm p) ss)

-- dear god
liftTerm
  (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc p)))))))))))
  (If sb st sf) =
    If (liftTerm p sb) (liftTerm p st) (liftTerm p sf)

liftTerms : {ds : Vect n Nat} -> (ss : All Term ds) -> Vect n (Term (fst (upperBound ds)))
liftTerms {ds = ds} ss = zipWithToVect liftTerm (snd (upperBound ds)) ss

liftExTerms : (ss : Vect n (Ex Term)) -> Vect n (Term (fst (upperBound (map fst ss))))
liftExTerms ss = liftTerms (unzipEx ss)

E0 : b Z -> Ex b
E0 = E

-- I actually want %default covering here but it doesn't exist
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
        "Num" => return NUM
        "Bool" => return BOOL
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

mutual
  covering parseTerm : (Monad m, Catchable m String) => TermParser m
  parseTerm = do
    s <- parseAs <|>
      parseVariant <|>
      parseParenTerm <|>
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

  covering parseApp : (Monad m, Catchable m String) => Ex Term -> TermParser m
  parseApp f = do
    arg <- maybe (spaces1 *> (parseParenTerm <|> parseBool <|> parseNum <|> parseVar))
    case arg of
      Nothing => return f
      Just x => let [f', x'] = liftExTerms [f, x] in parseApp (E (f' :$ x'))

  covering parseVar : (Monad m, Catchable m String) => TermParser m
  parseVar = E0 . Var <$> guard (\ident => not (elem ident keywords)) parseIdent

  covering parseBool : (Monad m, Catchable m String) => TermParser m
  parseBool =
    case !parseIdent of
      "true" => return (E $ Bool {d = 2} True)
      "false" => return (E $ Bool {d = 2} False)
      ident => failWith (ident ++ " isn't a bool literal")

  covering parseIf : (Monad m, Catchable m String) => TermParser m
  parseIf = do
    string "if" *> spaces1
    b <- parseTerm
    spaces1 *> string "then" *> spaces1
    t <- parseTerm
    spaces1 *> string "else" *> spaces1
    f <- parseTerm
    let [b', t', f'] = liftExTerms [b, t, f]
    return $ E $ If b' t' f'

  covering parseAs : (Monad m, Catchable m String) => TermParser m
  parseAs = do
    E t <- parseVariant <|>
      parseParenTerm <|>
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
    return $ E $ t `As` ty

  covering parseNum : (Monad m, Catchable m String) => TermParser m
  parseNum = do
    x <- parseNat
    return $ E0 $ Num x

  covering parseLam : (Monad m, Catchable m String) => TermParser m
  parseLam = do
    token '\\' *> spaces
    var <- parseIdent
    spaces *> token ':' *> spaces
    ty <- parseTy
    token '.' *> spaces
    E expr <- parseTerm
    return $ E $ Lam var ty expr

  covering parseLamRec : (Monad m, Catchable m String) => TermParser m
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
    E expr <- parseTerm
    return $ E $ LamRec vf v a b expr

  covering parseLet : (Monad m, Catchable m String) => TermParser m
  parseLet = do
    string "let" *> spaces
    parseUnpackingLet <|> parseSimpleLet
  where
    parseUnpackingLet : (Monad m, Catchable m String) => TermParser m
    parseUnpackingLet = do
      vs <- between (token '(') (token ')') (sep1 (spaces *> token ',' *> spaces) parseIdent)
      spaces *> token '=' *> spaces
      E s <- parseTerm
      spaces1 *> string "in" *> spaces1
      E t <- parseTerm
      let [s', t'] = liftTerms [s, t]
      return $ E $ Unpack (toVect vs) s' t'

    parseSimpleLet : (Monad m, Catchable m String) => TermParser m
    parseSimpleLet = do
      v <- parseIdent
      spaces *> token '=' *> spaces
      E s <- parseTerm
      spaces1 *> string "in" *> spaces1
      E t <- parseTerm
      let [s', t'] = liftTerms [s, t]
      return $ E $ Let v (liftTerm lteS s') t'

  covering parseCase : (Monad m, Catchable m String) => TermParser m
  parseCase = do
    string "case" *> spaces1
    s <- parseTerm
    spaces1 *> string "of" *> spaces1
    token '{' *> spaces
    let separator = spaces *> token ';' *> spaces
    ss <- sep1 separator parseTerm
    maybe separator *> spaces *> token '}'
    let (s' :: ss') = liftExTerms (s :: toVect ss)
    return $ E $ Case s' ss'

  covering parseVariant : (Monad m, Catchable m String) => TermParser m
  parseVariant = do
    string "variant" *> spaces1
    i <- parseNat
    spaces1
    E s <- parseVariant <|>
      parseParenTerm <|>
      parseLamRec <|>
      parseLet <|>
      parseLam <|>
      parseNum <|>
      parseBool <|>
      parseIf <|>
      parseCase <|>
      parseVar
    return $ E $ Variant i s

  covering parseParenTerm : (Monad m, Catchable m String) => TermParser m
  parseParenTerm = do
    token '(' *> spaces
    expr <- parseTerm
    parseTuple expr <|> parseEndParen expr
  where
    parseEndParen : (Monad m, Catchable m String) => Ex Term -> TermParser m
    parseEndParen expr = do
      spaces *> token ')'
      return expr

    parseTuple : (Monad m, Catchable m String) => Ex Term -> TermParser m
    parseTuple x = do
      let separator = spaces *> token ',' *> spaces
      xs <- separator *> sep1 separator parseTerm
      token ')'
      return $ E $ Tuple (liftExTerms (x :: toVect xs))

covering parseDef : (Monad m, Catchable m String) => StringParser m (String, Ex Term)
parseDef = do
  string "def" *> spaces1
  name <- parseIdent
  spaces1 *> token '=' *> spaces1
  s <- parseTerm
  return (name, s)
