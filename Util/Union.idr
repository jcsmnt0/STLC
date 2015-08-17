module Util.Union

import Data.Vect

data Union : Vect n Type -> Type where
  Inj : Elem a as -> a -> Union as

weaken : Union as -> Union (a :: as)
weaken (Inj p x) = Inj (There p) x
