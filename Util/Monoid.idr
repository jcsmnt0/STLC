module Util.Monoid

import Data.Vect

sepConcat : Monoid a => a -> Vect n a -> a
sepConcat _ [] = neutral
sepConcat _ [x] = x
sepConcat sep (x :: xs) = x <+> sep <+> sepConcat sep xs
