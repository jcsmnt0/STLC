module Util.LTE

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
