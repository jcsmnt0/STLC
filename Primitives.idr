module Primitives

import Data.Vect
import Data.Vect.Quantifiers

import Partial
import Term
import Ty

import Util.All

%default total

builtinSigs : Vect 14 (String, Ty)
builtinSigs =
  [ ("iszero", Num :-> Bool)
  , ("+", Num :-> Num :-> Num)
  , ("-", Num :-> Num :-> Num)
  , ("*", Num :-> Num :-> Num)
  , ("/", Num :-> Num :-> Num)
  , ("==", Num :-> Num :-> Bool) 
  , ("<", Num :-> Num :-> Bool)
  , ("<=", Num :-> Num :-> Bool)
  , (">", Num :-> Num :-> Bool)
  , (">=", Num :-> Num :-> Bool)
  , ("!=", Num :-> Num :-> Bool)
  , ("!", Bool :-> Bool)
  , ("=", Bool :-> Bool :-> Bool)
  , ("/=", Bool :-> Bool :-> Bool)
  ]

builtinNames : Vect (length Primitives.builtinSigs) String
builtinNames = map fst builtinSigs

builtinTys : Vect (length Primitives.builtinSigs) Ty
builtinTys = map snd builtinSigs

iszero : Term (S (S d)) (Num :: g) Bool
iszero = Prim [Num] Bool (\[x] => Now $ x == 0) (Tuple [Var "x" Here])

plus : Term (S (S d)) (Num :: Num :: g) Num
plus = Prim [Num, Num] Num (\[x, y] => Now $ x + y) (Tuple [Var "x" (There Here), Var "y" Here])

minus : Term (S (S d)) (Num :: Num :: g) Num
minus = Prim [Num, Num] Num (\[x, y] => Now $ x - y) (Tuple [Var "x" (There Here), Var "y" Here])

times : Term (S (S d)) (Num :: Num :: g) Num
times = Prim [Num, Num] Num (\[x, y] => Now $ x * y) (Tuple [Var "x" (There Here), Var "y" Here])

div : Term (S (S d)) (Num :: Num :: g) Num
div = Prim [Num, Num] Num (\[x, y] => Now $ x / y) (Tuple [Var "x" (There Here), Var "y" Here])

eqNum : Term (S (S d)) (Num :: Num :: g) Bool
eqNum = Prim [Num, Num] Bool (\[x, y] => Now $ x == y) (Tuple [Var "x" (There Here), Var "y" Here])

lt : Term (S (S d)) (Num :: Num :: g) Bool
lt = Prim [Num, Num] Bool (\[x, y] => Now $ x < y) (Tuple [Var "x" (There Here), Var "y" Here])

lte : Term (S (S d)) (Num :: Num :: g) Bool
lte = Prim [Num, Num] Bool (\[x, y] => Now $ x <= y) (Tuple [Var "x" (There Here), Var "y" Here])

gt : Term (S (S d)) (Num :: Num :: g) Bool
gt = Prim [Num, Num] Bool (\[x, y] => Now $ x > y) (Tuple [Var "x" (There Here), Var "y" Here])

gte : Term (S (S d)) (Num :: Num :: g) Bool
gte = Prim [Num, Num] Bool (\[x, y] => Now $ x >= y) (Tuple [Var "x" (There Here), Var "y" Here])

neqNum : Term (S (S d)) (Num :: Num :: g) Bool
neqNum = Prim [Num, Num] Bool (\[x, y] => Now $ x /= y) (Tuple [Var "x" (There Here), Var "y" Here])

not : Term (S (S d)) (Bool :: g) Bool
not = Prim [Bool] Bool (\[x] => Now $ not x) (Tuple [Var "x" Here])

eqBool : Term (S (S d)) (Bool :: Bool :: g) Bool
eqBool = Prim [Bool, Bool] Bool (\[x, y] => Now $ x == y) (Tuple [Var "x" (There Here), Var "y" Here])

neqBool : Term (S (S d)) (Bool :: Bool :: g) Bool
neqBool = Prim [Bool, Bool] Bool (\[x, y] => Now $ x /= y) (Tuple [Var "x" (There Here), Var "y" Here])

builtinTerms : All (Term 4 []) Primitives.builtinTys
builtinTerms =
  [ Lam "x" iszero
  , Lam "x" (Lam "y" plus)
  , Lam "x" (Lam "y" minus)
  , Lam "x" (Lam "y" times)
  , Lam "x" (Lam "y" div)
  , Lam "x" (Lam "y" eqNum)
  , Lam "x" (Lam "y" lt)
  , Lam "x" (Lam "y" lte)
  , Lam "x" (Lam "y" gt)
  , Lam "x" (Lam "y" gte)
  , Lam "x" (Lam "y" neqNum)
  , Lam "x" not
  , Lam "x" (Lam "y" eqBool)
  , Lam "x" (Lam "y" neqBool)
  ]

partial builtinVals : All Val Primitives.builtinTys
builtinVals = mapId {ps = builtinTys} (impatience . eval []) builtinTerms
