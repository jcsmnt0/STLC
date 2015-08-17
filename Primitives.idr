module Primitives

import Data.Vect

import Partial
import PiVect
import Term
import Ty

%default total

builtinSigs : Vect 13 (String, Ty)
builtinSigs =
  [ ("+", Num :-> Num :-> Num)
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

builtinNames : Vect (length builtinSigs) String
builtinNames = map fst builtinSigs

builtinTys : Vect (length builtinSigs) Ty
builtinTys = map snd builtinSigs

plus : Term (S d) (Num :: Num :: g) Num
plus = Prim [Num, Num] Num (\[x, y] => Now $ x + y) [Var "x" (There Here), Var "y" Here]

minus : Term (S d) (Num :: Num :: g) Num
minus = Prim [Num, Num] Num (\[x, y] => Now $ x - y) [Var "x" (There Here), Var "y" Here]

times : Term (S d) (Num :: Num :: g) Num
times = Prim [Num, Num] Num (\[x, y] => Now $ x * y) [Var "x" (There Here), Var "y" Here]

div : Term (S d) (Num :: Num :: g) Num
div = Prim [Num, Num] Num (\[x, y] => Now $ x / y) [Var "x" (There Here), Var "y" Here]

eqNum : Term (S d) (Num :: Num :: g) Bool
eqNum = Prim [Num, Num] Bool (\[x, y] => Now $ x == y) [Var "x" (There Here), Var "y" Here]

lt : Term (S d) (Num :: Num :: g) Bool
lt = Prim [Num, Num] Bool (\[x, y] => Now $ x < y) [Var "x" (There Here), Var "y" Here]

lte : Term (S d) (Num :: Num :: g) Bool
lte = Prim [Num, Num] Bool (\[x, y] => Now $ x <= y) [Var "x" (There Here), Var "y" Here]

gt : Term (S d) (Num :: Num :: g) Bool
gt = Prim [Num, Num] Bool (\[x, y] => Now $ x > y) [Var "x" (There Here), Var "y" Here]

gte : Term (S d) (Num :: Num :: g) Bool
gte = Prim [Num, Num] Bool (\[x, y] => Now $ x >= y) [Var "x" (There Here), Var "y" Here]

neqNum : Term (S d) (Num :: Num :: g) Bool
neqNum = Prim [Num, Num] Bool (\[x, y] => Now $ x /= y) [Var "x" (There Here), Var "y" Here]

not : Term (S d) (Bool :: g) Bool
not = Prim [Bool] Bool (\[x] => Now $ not x) [Var "x" Here]

eqBool : Term (S d) (Bool :: Bool :: g) Bool
eqBool = Prim [Bool, Bool] Bool (\[x, y] => Now $ x == y) [Var "x" (There Here), Var "y" Here]

neqBool : Term (S d) (Bool :: Bool :: g) Bool
neqBool = Prim [Bool, Bool] Bool (\[x, y] => Now $ x /= y) [Var "x" (There Here), Var "y" Here]

-- well damn - typechecking these is (figuratively, but practically) interminable
builtinTerms : PiVect (Term 4 []) (map snd builtinSigs)
builtinTerms =
  [ Lam "x" (Lam "y" plus)
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

partial builtinVals : PiVect Val builtinTys
builtinVals = mapId {ps = builtinTys} (impatience . eval []) builtinTerms
