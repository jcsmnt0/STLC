module Primitives

import Data.Vect

import Partial
import PiVect
import Term
import Ty

%default total

builtinSigs : Vect 3 (String, Ty)
builtinSigs =
  [ ("+", Num :-> Num :-> Num)
  , ("-", Num :-> Num :-> Num)
  , ("*", Num :-> Num :-> Num)
  -- , ("/", Num :-> Num :-> Num)
  -- , ("==", Num :-> Num :-> Bool) 
  -- , ("<", Num :-> Num :-> Bool)
  -- , ("<=", Num :-> Num :-> Bool)
  -- , (">", Num :-> Num :-> Bool)
  -- , (">=", Num :-> Num :-> Bool)
  -- , ("!=", Num :-> Num :-> Bool)
  -- , ("!", Bool :-> Bool)
  -- , ("=", Bool :-> Bool :-> Bool)
  -- , ("/=", Bool :-> Bool :-> Bool)
  ]

builtinNames : Vect (length builtinSigs) String
builtinNames = map fst builtinSigs

builtinTys : Vect (length builtinSigs) Ty
builtinTys = map snd builtinSigs

-- well damn - typechecking these is (figuratively, but practically) interminable
builtinTerms : PiVect (Term 4 []) (map snd builtinSigs)
builtinTerms =
  [ Lam "x"
      (Lam "y"
        (Prim [Num, Num] Num (\[x, y] => Now $ x + y) [Var "x" (There Here), Var "y" Here]))

  , Lam "x"
      (Lam "y"
        (Prim [Num, Num] Num (\[x, y] => Now $ x - y) [Var "x" (There Here), Var "y" Here]))

  , Lam "x"
      (Lam "y"
        (Prim [Num, Num] Num (\[x, y] => Now $ x * y) [Var "x" (There Here), Var "y" Here]))

  -- , Lam "x"
  --     (Lam "y"
  --       (Prim [Num, Num] Num (\[x, y] => Now $ x / y) [Var "x" (There Here), Var "y" Here]))

  -- , Lam "x"
  --     (Lam "y"
  --       (Prim [Num, Num] Bool (\[x, y] => Now $ x == y) [Var "x" (There Here), Var "y" Here]))

  -- , Lam "x"
  --     (Lam "y"
  --       (Prim [Num, Num] Bool (\[x, y] => Now $ x < y) [Var "x" (There Here), Var "y" Here]))

  -- , Lam "x"
  --     (Lam "y"
  --       (Prim [Num, Num] Bool (\[x, y] => Now $ x <= y) [Var "x" (There Here), Var "y" Here]))

  -- , Lam "x"
  --     (Lam "y"
  --       (Prim [Num, Num] Bool (\[x, y] => Now $ x > y) [Var "x" (There Here), Var "y" Here]))

  -- , Lam "x"
  --     (Lam "y"
  --       (Prim [Num, Num] Bool (\[x, y] => Now $ x >= y) [Var "x" (There Here), Var "y" Here]))

  -- , Lam "x"
  --     (Lam "y"
  --       (Prim [Num, Num] Bool (\[x, y] => Now $ x /= y) [Var "x" (There Here), Var "y" Here]))

  -- , Lam "x"
  --     (Prim [Bool] Bool (\[x] => Now $ not x) [Var "x" Here])

  -- , Lam "x"
  --     (Lam "y"
  --       (Prim [Bool, Bool] Bool (\[x, y] => Now $ x == y) [Var "x" (There Here), Var "y" Here]))

  -- , Lam "x"
  --     (Lam "y"
  --       (Prim [Bool, Bool] Bool (\[x, y] => Now $ x /= y) [Var "x" (There Here), Var "y" Here]))
  ]

partial builtinVals : PiVect Val builtinTys
builtinVals = mapId {ps = builtinTys} (impatience . eval []) builtinTerms
