module Primitives

import Data.Vect
import Data.Vect.Quantifiers

import Term.Eval
import Term.Typed
import Ty.Raw
import Ty.Scoped
import Ty.Val

import Util.All
import Util.Partial

%default total

export
primitiveSigs : Vect 3 (String, Raw.Ty)
primitiveSigs =
  [ ("iszero", NUM :-> BOOL)
  , ("suc", NUM :-> NUM)
  , ("pred", NUM :-> NUM)
  ]

export
primitiveNames : Vect (length Primitives.primitiveSigs) String
primitiveNames = map fst primitiveSigs

export
primitiveTys : Vect (length Primitives.primitiveSigs) Raw.Ty
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

export
primitiveVals : All (SynVal []) Primitives.primitiveTys
primitiveVals = map' (impatience . eval [] []) primitiveTerms
