module Util.Union

import Data.Vect

public export
data Union : Vect n Type -> Type where
  Inj : Elem a as -> a -> Union as

export
weaken : Union as -> Union (a :: as)
weaken (Inj p x) = Inj (There p) x
