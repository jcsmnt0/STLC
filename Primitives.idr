module Primitives

import Data.Vect
import Data.Vect.Quantifiers

import Partial
import Syntax
import Term
import Ty

import Util.All

%default total

primitiveSigs : Vect 3 (String, SynTy)
primitiveSigs =
  [ ("iszero", NUM :-> BOOL)
  , ("suc", NUM :-> NUM)
  , ("pred", NUM :-> NUM)
  ]

primitiveNames : Vect (length Primitives.primitiveSigs) String
primitiveNames = map fst primitiveSigs

primitiveTys : Vect (length Primitives.primitiveSigs) SynTy
primitiveTys = map snd primitiveSigs

iszero : SynTerm (4 + d) 0 g (NUM :-> BOOL)
iszero = Lam $ Prim (bool . (== 0)) (Var 0)

suc : SynTerm (5 + d) 0 g (NUM :-> NUM)
suc = Lam $ Prim (C' . S) (Var 0)

pred : SynTerm (5 + d) 0 g (NUM :-> NUM)
pred = Lam $ Prim (C' . Nat.pred) (Var 0)

%default partial

primitiveTerms : All (SynTerm 6 0 []) Primitives.primitiveTys
primitiveTerms =
  [ iszero {g = []}
  , suc {g = []}
  , pred {g = []}
  ]

primitiveVals : All (SynVal []) Primitives.primitiveTys
primitiveVals = map' {ps = primitiveTys} (impatience . eval [] []) primitiveTerms
