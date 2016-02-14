module Show

import Data.Fin
import Data.Vect
import Data.Vect.Quantifiers

import ParseSyntax
import Partial
import Scopecheck
import Syntax
import Term
import Ty
import Typecheck

import Util.All
import Util.Elem
import Util.Ex
import Util.Fin
import Util.Union

%default total

Show Ty where
  show Bool = "Bool"
  show Num = "Num"
  show (Tuple tys) = "(" ++ concat (intersperse ", " (map (assert_total show) tys)) ++ ")"
  show (Sum tys) = "(" ++ concat (intersperse " | " (map (assert_total show) tys)) ++ ")"
  show ((s :-> t) :-> r) = "(" ++ show (s :-> t) ++ ")" ++ " -> " ++ show r
  show (s :-> t) = show s ++ " -> " ++ show t

-- this probably gets parentheses wrong sometimes
Show (Syn d) where
  show (Var v) = v
  show (Num x) = show x
  show (Bool x) = if x then "true" else "false"
  show (LamRec vf a v b s) = "(fn " ++ vf ++ "(" ++ v ++ ": " ++ show a ++ "): " ++ show b ++ ". " ++ show s ++ ")"
  show (Lam name ty body) = "\\" ++ name ++ ": " ++ show ty ++ ". " ++ show body
  show (Lam v ty x :$ Lam v' ty' x') = "(" ++ show (Lam v ty x) ++ ") (" ++ show (Lam v' ty' x') ++ ")"
  show (x :$ Lam v ty y) = show x ++ " (" ++ show (Lam v ty y) ++ ")"
  show (Lam v ty x :$ (y :$ z)) = "(" ++ show (Lam v ty x) ++ ") (" ++ show (y :$ z) ++ ")"
  show (Lam v ty x :$ y) = "(" ++ show (Lam v ty x) ++ ") " ++ show y
  show (x :$ (y :$ z)) = show x ++ " (" ++ show (y :$ z) ++ ")"
  show (x :$ y) = show x ++ " " ++ show y
  show (If b t f) = "if " ++ show b ++ " then " ++ show t ++ " else " ++ show f
  show (Tuple xs) = "(" ++ concat (intersperse ", " (map show xs)) ++ ")"
  show (Variant i s) = "variant " ++ show i ++ " " ++ show s
  show (Case s ss) = "case " ++ show s ++ " of { " ++ concat (intersperse "; " (map (\(v, s) => v ++ " => " ++ show ss) ss))
  show (Let v s t) = "let " ++ v ++ " = " ++ show s ++ " in " ++ show t
  show (Unpack vs s t) = "let (" ++ concat (intersperse ", " vs) ++ ") = " ++ show s ++ " in " ++ show t
  show (s `As` ty) = "(" ++ show s ++ " : " ++ show ty ++ ")"

total strip : Term d gty t -> Syn d
strip (Bool x) = Bool x
strip (Num x) = Num x
strip (Var v _) = Var v
strip (Lam v {b = b} x) = Lam v b (strip x)
strip (LamRec vf v {a = a} {b = b} tm) = LamRec vf a v b (strip tm)
strip (x :$ y) = strip x :$ strip y
strip (If b t f) = If (strip b) (strip t) (strip f)
strip (Tuple xs) = Tuple (mapToVect strip xs)
strip (Variant {as = as} i tm) = Variant (finToNat (toFin i)) (strip tm)
strip (Case s vs ss) = Case (strip s) (zip vs (mapToVect strip ss))
strip (Unpack vs s t) = Unpack vs (strip s) (strip t)
strip (Prim _ _ _ _) = Var "<primitive thing>"

Show (Term d gty t) where
  show {t = t} tm = show (strip tm)

mutual
  showTuple : Val (Tuple as) -> String
  showTuple xs = "(" ++ concat (intersperse ", " (mapToVect (assert_total showVal) xs)) ++ ")"
  
  showSum : Nat -> Val (Sum as) -> String
  showSum {as = a :: as} i (Inj Here x) = Foldable.concat $ the (List String)
    [ "(variant "
    , show i
    , " "
    , assert_total (showVal x)
    , " : ("
    , concat (intersperse " | " (map show (a :: as)))
    , "))"
    ]
  showSum {as = a :: as} i (Inj (There p) x) = showSum (S i) (Inj p x)
  
  showVal : Val a -> String
  showVal {a = Bool} x = show x
  showVal {a = Num} x = show x
  showVal {a = Tuple as} xs = showTuple xs
  showVal {a = Sum as} x = showSum 0 x
  showVal {a = a :-> b} f = "function"

showExVal : Ex Val -> String
showExVal (E {x = a} x) = showVal x ++ " : " ++ show a

Show TypeError where
  show err = "type error: " ++
    case err of
      App => "app"
      If => "if"
      Variant => "variant"
      LamRec => "lam rec"
      As s ty ty' => show (unscope s) ++ " is of type " ++ show ty' ++ " but should be of type " ++ show ty
      CantInfer => "can't infer"
      Case => "case"
      Unpack => "unpack"
