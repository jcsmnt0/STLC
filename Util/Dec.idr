module Util.Dec

Show a => Show (Dec a) where
  show (Yes x) = "Yes " ++ show x
  show (No _) = "No"

infixl 4 =?
(=?) : DecEq a => (x, y : a) -> Dec (x = y)
(=?) = decEq

interface Requires a b where
  because : Not b -> Not a

map : Requires b a => (a -> b) -> Dec a -> Dec b
map f (Yes x) = Yes (f x)
map _ (No contra) = No (because contra)

(>>=) : Requires b a => Dec a -> (a -> Dec b) -> Dec b
(Yes x) >>= f = f x
(No contra) >>= f = No (because contra)
