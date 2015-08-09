module TagSyntaxDepth

import ParseSyntax
import PiVect
import Syntax
import Ty

tagDepth :
  RawSyn ->
  (d ** Syn d)

tagDepth (Var v) =
  (Z ** Var v)

tagDepth (Num x) =
  (Z ** Num x)

tagDepth (Bool x) =
  (Z ** Bool x)

tagDepth (Lam v ty r) =
  let (d ** s) = tagDepth r in
    (S d ** Lam v ty s)

tagDepth (rx :$ ry) =
  let (dx ** sx) = tagDepth rx in
  let (dy ** sy) = tagDepth ry in
  let (d ** [px, py]) = upperBound [dx, dy] in
    (S d ** lift px sx :$ lift py sy)

tagDepth (If rb rt rf) =
  let (db ** sb) = tagDepth rb in
  let (dt ** st) = tagDepth rt in
  let (df ** sf) = tagDepth rf in
  let (d ** [pb, pt, pf]) = upperBound [db, dt, df] in
    (S d ** If (lift pb sb) (lift pt st) (lift pf sf))

{- assert_total is necessary here because RawSyn isn't tagged with depth information, so there's no argument to
   tagDepth that decreases in size in the expression "map tagDepth" that the totality checker can latch
   onto. This should be total because it should be impossible to build an infinitely deep RawSyn value via any
   total computation, and the totality checker will catch the case where it's called on a RawSyn constructed by
   a partial (or non-totality-checkable) computation. -}
tagDepth (Tuple rs) =
  let (ds ** ss) = unzipToPiVect (map (assert_total tagDepth) rs) in
  let (d ** ps) = upperBound ds in
    (S d ** Tuple (zipWithIdToVect (lift {n = d}) ps ss))
