module Show

import Data.Fin
import Data.Vect

import ParseSyntax
import Partial
import PiVect
import Scopecheck
import Syntax
import Term
import Ty
import Typecheck

import Util.Elem
import Util.Ex
import Util.Fin
import Util.Monoid

%default partial -- should be %default covering but that doesn't exist?

instance Show Ty where
  show Bool = "Bool"
  show Num = "Num"
  show (Tuple tys) = "(" ++ sepConcat ", " (map show tys) ++ ")"
  show (Sum tys) = "(" ++ sepConcat " | " (map show tys) ++ ")"
  show ((s :-> t) :-> r) = "(" ++ show (s :-> t) ++ ")" ++ " -> " ++ show r
  show (s :-> t) = show s ++ " -> " ++ show t

instance Show (Syn d) where
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
  show (Tuple xs) = "(" ++ sepConcat ", " (map show xs) ++ ")"
  show (Variant i s) = "variant " ++ show i ++ " " ++ show s
  show (Case s ss) = "case " ++ show s ++ " of { " ++ sepConcat "; " (map (\(v, s) => v ++ " => " ++ show ss) ss)
  show (s `As` ty) = "(" ++ show s ++ " : " ++ show ty ++ ")"

covering strip : Term d gty t -> Syn d
strip (Bool x) = Bool x
strip (Num x) = Num x
strip (Var v _) = Var v
strip (Lam v {b = b} x) = Lam v b (strip x)
strip (LamRec vf v {a = a} {b = b} tm) = LamRec vf a v b (strip tm)
strip (x :$ y) = strip x :$ strip y
strip (If b t f) = If (strip b) (strip t) (strip f)
strip (Tuple xs) = Tuple (mapToVect strip xs)
strip (Variant {as = as} i tm) = Variant (finToNat (toFin i)) (strip tm) `As` Sum as
strip (Case s vs ss) = Case (strip s) (zip vs (mapToVect strip ss))
strip (Prim _ _ _ _) = Var "<primitive thing>"

instance Show (Term d gty t) where
  show {t = t} tm = show (strip tm)

instance Show (Val t) where
  show (Bool x) = show x
  show (Num x) = show x
  show (Cls {a = a} v p x) = "\\" ++ v ++ ": " ++ show a ++ ". " ++ show (strip x)
  show (ClsRec {a = a} {b = b} vf v p s) = "fn " ++ vf ++ "(" ++ v ++ ": " ++ show a ++ "): " ++ show b ++ ". " ++ show (strip s) ++ ")"
  show (Tuple xs) = "(" ++ sepConcat ", " (mapToVect (\x => show x) xs) ++ ")"
  show (Variant {as = as} _ x) = "(" ++ show x ++ " : (" ++ sepConcat " | " (map show as) ++ "))"

instance Show TypeError where
  show err = "type error: " ++
    case err of
      App => "app"
      If => "if"
      Variant => "variant"
      As s ty ty' => show (unscope s) ++ " is of type " ++ show ty' ++ " but should be of type " ++ show ty
      Case => "case"
