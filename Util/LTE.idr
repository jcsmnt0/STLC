module Util.LTE

import Data.Vect
import Data.Vect.Quantifiers

%default total

export
decLTE : (m, n : Nat) -> Either (LTE m n) (LTE n m)
decLTE Z _ = Left LTEZero
decLTE _ Z = Right LTEZero
decLTE (S m) (S n) =
  case decLTE m n of
    Left lte => Left (LTESucc lte)
    Right lte => Right (LTESucc lte)

id : x `LTE` x
id {x = Z} = LTEZero
id {x = S _} = LTESucc id

trans : x `LTE` y -> y `LTE` z -> x `LTE` z
trans LTEZero q = LTEZero
trans (LTESucc p) (LTESucc q) = LTESucc (trans p q)

export
lteS : x `LTE` S x
lteS {x = Z} = LTEZero
lteS {x = S _} = LTESucc lteS

ltePlus : (z : Nat) -> LTE x y -> LTE (z + x) (z + y)
ltePlus Z = id
ltePlus (S _) = LTESucc . ltePlus _

raise : All (\x => x `LTE` y) xs -> y `LTE` z -> All (\x => x `LTE` z) xs
raise {xs = []} [] _ = []
raise {xs = _ :: _} (p :: ps) q = trans p q :: raise ps q

public export
upperBound : (xs : Vect n Nat) -> (y ** All (\x => x `LTE` y) xs)
upperBound [] = (Z ** [])
upperBound [x] = (x ** [lteRefl])
upperBound (x :: xs) =
  let (y ** ps) = upperBound xs in
    case decLTE x y of
      Left x_lte_y => (y ** x_lte_y :: ps)
      Right y_lte_x => (x ** lteRefl :: raise ps y_lte_x)
