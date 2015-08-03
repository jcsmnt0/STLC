module Util.Fin

import Data.Fin

instance Show (Fin n) where
  show = show . finToNat
