module Util.LTE

import Data.Vect
import Data.Vect.Quantifiers

%default total

decLTE : (m, n : Nat) -> Either (LTE m n) (LTE n m)
decLTE Z _ = Left LTEZero
decLTE _ Z = Right LTEZero
decLTE (S m) (S n) =
  case decLTE m n of
    Left lte => Left (LTESucc lte)
    Right lte => Right (LTESucc lte)

lteTrans : x `LTE` y -> y `LTE` z -> x `LTE` z
lteTrans LTEZero q = LTEZero
lteTrans (LTESucc p) (LTESucc q) = LTESucc (lteTrans p q)

lteSucc : LTE x (S x)
lteSucc {x = Z} = LTEZero
lteSucc {x = S _} = LTESucc lteSucc

raise : All (\x => x `LTE` y) xs -> y `LTE` z -> All (\x => x `LTE` z) xs
raise {xs = []} [] _ = []
raise {xs = _ :: _} (p :: ps) q = lteTrans p q :: raise ps q

upperBound : (xs : Vect n Nat) -> (y ** All (\x => x `LTE` y) xs)
upperBound [] = (Z ** [])
upperBound [x] = (x ** [lteRefl])
upperBound (x :: xs) =
  let (y ** ps) = upperBound xs in
    case decLTE x y of
      Left x_lte_y => (y ** x_lte_y :: ps)
      Right y_lte_x => (x ** lteRefl :: raise ps y_lte_x)
