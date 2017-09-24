module Util.Dec

%default total

infixl 4 =?

Show a => Show (Dec a) where
  show (Yes x) = "Yes " ++ show x
  show (No _) = "No"

export
(=?) : DecEq a => (x, y : a) -> Dec (x = y)
(=?) = decEq
