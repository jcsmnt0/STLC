module Tests

import Data.Fin
import Data.Vect
import Data.Vect.Quantifiers

import Partial
import Term
import Ty

import Util.Func

%default total

id : Term (2 + d) 1 g (0 :-> 0)
id = Lam $ Var 0

const : Term (2 + d) 2 g (0 :-> 1 :-> 0)
const = Lam $ Lam $ Var 1

comp : Term (5 + d) 3 g ((1 :-> 2) :-> (0 :-> 1) :-> 0 :-> 2)
comp = Lam (Lam (Lam (Var 2 :$ (Var 1 :$ Var 0))))

zero : Term (1 + d) 0 g (C Nat)
zero = C $ Now 0

suc : Term (2 + d) 0 g (C Nat :-> C Nat)
suc = Lam $ Prim (C . Now . (+ 1)) (Var 0)

pred : Term (2 + d) 0 g (C Nat :-> C Nat)
pred = Lam $ Prim (C . Now . Nat.pred) (Var 0)

twice : Term (4 + d) 1 g ((0 :-> 0) :-> 0 :-> 0)
twice = Lam (Lam (Var 1 :$ (Var 1 :$ Var 0)))

UNIT : Ty l
UNIT = Tuple []

unit : Term (1 + d) 0 g UNIT
unit = Tuple []

BOOL : Ty l
BOOL = Sum [UNIT, UNIT]

true : Term (2 + d) 0 g BOOL
true = Variant Here unit

false : Term (2 + d) 0 g BOOL
false = Variant (There Here) unit

iszero : Term (4 + d) 0 g (C Nat :-> BOOL)
iszero = Lam $ Prim (\x => if x == 0 then true else false) (Var 0)

LAZY : Ty l -> Ty l
LAZY a = UNIT :-> a

-- -- need opes on Terms
-- implicit delay : Term d 0 g a -> Term (S d) 0 g (LAZY a)
-- delay t = Lam $ weaken t

-- -- change the return type of Prim's func to be a Term b, that way it even looks kind of like a bind and this works
-- prim_bool : Term (2 + d) 0 g (C Bool :-> BOOL)
-- prim_bool = Lam $ Prim' (\x => if x then true else false) [Var 0]

if' : Term (7 + d) 1 g (BOOL :-> LAZY 0 :-> LAZY 0 :-> 0)
if' = Lam $ Lam $ Lam $ Case (Var 2)
  [ Var 1
  , Var 0
  ]

plus : Term (12 + d) 0 g (C Nat :-> C Nat :-> C Nat)
plus =
  LamRec
    (if' :@ (C Nat :-> C Nat) :$
      (iszero :$ Var 1) :$
      (Lam (Lam (Var 0))) :$
      (Lam (Lam (Var 2 :$ (pred :$ Var 3) :$ (suc :$ Var 0)))))

countdown : Term (12 + d) 0 g (C Nat :-> C Nat)
countdown =
  LamRec
    (if' :@ C Nat :$
      (iszero :$ Var 1) :$
      (Lam (C $ Now 0)) :$
      (Lam (Var 1 :$ (pred :$ Var 2))))

-- isOne : Term (2 + d) 0 g (C Nat :-> C Bool)
-- isOne = Lam $ Prim' (== 1) [Var 0]

-- factorial : Term (9 + d) 0 g (C Nat :-> C Nat)
-- factorial =
--   (LamRec
--     (ifnat :$
--       (isOne :$ Var 1) :$
--       Var 1 :$
--       (times :$
--         Var 1 :$
--         (Var 0 :$
--           (minus :$
--             Var 1 :$
--             C 1)))))
