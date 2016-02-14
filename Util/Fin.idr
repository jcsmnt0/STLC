module Util.Fin

import Data.Fin

Show (Fin n) where
  show = show . finToNat
