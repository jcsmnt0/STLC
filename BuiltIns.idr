module BuiltIns

import Control.Catchable
import Control.Monad.State
import Data.Fin

import Term.Raw
import Term.Parse
import Term.Typecheck
import Ty.Raw

import Interpreter

import Util.Ex

%default partial
%access export

-- just some arbitrary depth large enough for all of these terms
E' : Raw.Term 100 -> Ex Raw.Term
E' = E

private implicit var : String -> Raw.Term d
var = Var

private implicit bool : Bool -> Raw.Term (2 + d)
bool = Bool

private fromInteger : (x : Integer) -> {default ItIsJust p : IsJust (integerToFin x l)} -> Raw.Term l
fromInteger x = Num $ fromInteger x

-- there's probably a way to use dsl notation for Lam
builtinEnv : (MonadState Env m, Catchable m String, Catchable m TypeError, Monad m) => m Env
builtinEnv = interpretEnv
  [ ("idNat", E' $ Lam "x" NUM "x")

  , ("+", E' $
      LamRec "+" "x" NUM (NUM :-> NUM)
        (If
          ("iszero" :$ "x")
          "idNat"
          (Lam "y" NUM
            ("+" :$ ("pred" :$ "x") :$ ("suc" :$ "y")))))

  , ("-", E' $
      LamRec "-" "x" NUM (NUM :-> NUM)
        (Lam "y" NUM
          (If
            ("iszero" :$ "y")
            ("x")
            ("-" :$ ("pred" :$ "x") :$ ("pred" :$ "y")))))

  , ("*", E' $
      LamRec "*" "x" NUM (NUM :-> NUM)
        (Lam "y" NUM
          (If
            ("iszero" :$ "x")
            0
              ("+" :$ "y" :$ ("*" :$ ("pred" :$ "x") :$ "y")))))

  , ("&&", E' $
      Lam "x" BOOL
        (Lam "y" BOOL
          (If "x" "y" False)))

  , ("||", E' $
      Lam "x" BOOL
        (Lam "y" BOOL
          (If "x" True "y")))

  , ("==", E' $
      LamRec "==" "x" NUM (NUM :-> BOOL)
        (Lam "y" NUM
          (If
            ("&&" :$ ("iszero" :$ "x") :$ ("iszero" :$ "y"))
            True
            (If
              ("iszero" :$ "x")
              False
              (If
                ("iszero" :$ "y")
                False
                ("==" :$ ("pred" :$ "x") :$ ("pred" :$ "y")))))))
  ]
