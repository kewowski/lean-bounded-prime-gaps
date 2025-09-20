/-
  Sieve/Stage2BoundsFromEq.lean
  Build Stage-2 moment bounds from exact equalities.
-/
import Mathlib
import Sieve.MaynardWeights
import Sieve.MTMoments
import Sieve.Stage2Weight

noncomputable section
open Classical

namespace Sieve.Stage2Weight

/-- If you know exact equalities
    `firstMoment W = (#support) · M` and `secondMoment W = (#support) · M2`,
    you can package them as Stage-2 `MomentBounds W`. -/
def bounds_of_equalities
    (W  : Sieve.MaynardWeights.Weight)
    (M  : ℝ) (h1 : Sieve.MTMoments.firstMoment W = (W.support.card : ℝ) * M)
    (M2 : ℝ) (h2 : Sieve.MTMoments.secondMoment W = (W.support.card : ℝ) * M2)
    : MomentBounds W :=
{ M  := M,
  M2 := M2,
  first_le  := le_of_eq h1,
  second_le := le_of_eq h2 }

end Sieve.Stage2Weight
