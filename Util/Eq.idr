module Util.Eq

import Util.Dec

instance Requires (x = y) (y = x) where
  because contra Refl = contra Refl

replacePreservesEquality : {P : a -> Type} -> (x : P u) -> (p : u = v) -> x = replace {P = P} p x
replacePreservesEquality x Refl = Refl
