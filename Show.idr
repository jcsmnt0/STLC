module Show

import Data.Fin
import Data.HVect
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
import Util.Eq
import Util.Ex
import Util.Fin
import Util.Union

%default total

Show SynTy where
  show NUM = "Num"
  show (Sum [Tuple [], Tuple []]) = "Bool"
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
  show (Case s ss) = "case " ++ show s ++ " of { " ++ concat (intersperse "; " (map show ss)) ++ " }"
  show (Let v s t) = "let " ++ v ++ " = " ++ show s ++ " in " ++ show t
  show (Unpack vs s t) = "let (" ++ concat (intersperse ", " vs) ++ ") = " ++ show s ++ " in " ++ show t
  show (s `As` ty) = "(" ++ show s ++ " : " ++ show ty ++ ")"

mutual
  showTuple : (as : Vect n SynTy) -> SynVal e (Tuple as) -> String
  showTuple as xs = "(" ++ showTuple' as xs ++ ")"
    where
      showTuple' : (as : Vect n SynTy) -> SynVal e (Tuple as) -> String
      showTuple' [] [] = ""
      showTuple' [a] [x] = assert_total (showVal a x)
      showTuple' (a :: as) (x :: xs) = assert_total (showVal a x) ++ ", " ++ showTuple' as xs
  
  -- this is wrong (it strips off leading types)
  showSum : (as : Vect n SynTy) -> Nat -> SynVal e (Sum as) -> String
  showSum as i xs = concat $ the (List String) ["(variant ", show i, " ", showSum' as xs, ")"]
    where
      showSum' : (as : Vect n SynTy) -> SynVal e (Sum as) -> String
      showSum' (a :: _) (Inj Here x) = assert_total (showVal a x)
      showSum' (_ :: as) (Inj (There p) x) = showSum' as (Inj p x)

  showVal : (a : _) -> SynVal e a -> String
  showVal NUM x = show x
  showVal (Tuple as) xs = showTuple as xs
  showVal (Sum [Tuple [], Tuple []]) (Inj Here []) = "true"
  showVal (Sum [Tuple [], Tuple []]) (Inj (There Here) []) = "false"
  showVal (Sum as) x = showSum as 0 x
  showVal (a :-> b) f = "function"

showExVal : Ex (SynVal e) -> String
showExVal (E {x = a} x) = showVal a x ++ " : " ++ show a

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
