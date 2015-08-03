module Util.Eq

import Util.Dec

instance Requires (x = y) (y = x) where
  because contra Refl = contra Refl
