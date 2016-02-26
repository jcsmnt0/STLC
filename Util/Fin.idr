module Util.Fin

import Data.Fin

%default total

Show (Fin n) where
  show = show . finToNat
