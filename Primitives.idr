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

builtinTerms : PiVect (Term 4 []) (map snd builtinSigs)
builtinTerms =
  [ Lam "x"
      (Lam "y"
        (Match
          (Prim [Num, Num] Num (+))
          (Tuple [Var "x" (There Here), Var "y" Here])
          (Var "x + y" Here)))

  , Lam "x"
      (Lam "y"
        (Match
          (Prim [Num, Num] Num (-))
          (Tuple [Var "x" (There Here), Var "y" Here])
          (Var "x - y" Here)))

  , Lam "x"
      (Lam "y"
        (Match
          (Prim [Num, Num] Num (*))
          (Tuple [Var "x" (There Here), Var "y" Here])
          (Var "x * y" Here)))

  , Lam "x"
      (Lam "y"
        (Match
          (Prim [Num, Num] Num (/))
          (Tuple [Var "x" (There Here), Var "y" Here])
          (Var "x / y" Here)))

  , Lam "x"
      (Lam "y"
        (Match
          (Prim [Num, Num] Bool (==))
          (Tuple [Var "x" (There Here), Var "y" Here])
          (Var "x == y" Here)))

  , Lam "x"
      (Lam "y"
        (Match
          (Prim [Num, Num] Bool (<))
          (Tuple [Var "x" (There Here), Var "y" Here])
          (Var "x < y" Here)))

  , Lam "x"
      (Lam "y"
        (Match
          (Prim [Num, Num] Bool (<=))
          (Tuple [Var "x" (There Here), Var "y" Here])
          (Var "x <= y" Here)))

  , Lam "x"
      (Lam "y"
        (Match
          (Prim [Num, Num] Bool (>))
          (Tuple [Var "x" (There Here), Var "y" Here])
          (Var "x > y" Here)))

  , Lam "x"
      (Lam "y"
        (Match
          (Prim [Num, Num] Bool (>=))
          (Tuple [Var "x" (There Here), Var "y" Here])
          (Var "x >= y" Here)))

  , Lam "x"
      (Lam "y"
        (Match
          (Prim [Num, Num] Bool (/=))
          (Tuple [Var "x" (There Here), Var "y" Here])
          (Var "x /= y" Here)))

  , Lam "x"
      (Match
        (Prim [Bool] Bool not)
        (Tuple [Var "x" Here])
        (Var "!x" Here))

  , Lam "x"
      (Lam "y"
        (Match
          (Prim [Bool, Bool] Bool (==))
          (Tuple [Var "x" (There Here), Var "y" Here])
          (Var "x = y" Here)))

  , Lam "x"
      (Lam "y"
        (Match
          (Prim [Bool, Bool] Bool (/=))
          (Tuple [Var "x" (There Here), Var "y" Here])
          (Var "x /= y" Here)))
  ]

partial builtinVals : PiVect Val builtinTys
builtinVals = mapId {ps = builtinTys} (impatience . eval []) builtinTerms
