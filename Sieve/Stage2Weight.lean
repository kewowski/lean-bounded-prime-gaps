/-
  Sieve/Stage2Weight.lean
  Package moment bounds for a fixed Weight from simple pointwise caps.
-/
import Mathlib
import Sieve.MaynardWeights
import Sieve.MTMoments
import Sieve.MTMomentBounds

noncomputable section
open Classical

namespace Sieve.Stage2Weight

/-- Moment bounds for a specific `W`. -/
structure MomentBounds (W : Sieve.MaynardWeights.Weight) where
  M  : ℝ
  M2 : ℝ
  first_le  : Sieve.MTMoments.firstMoment W ≤ (W.support.card : ℝ) * M
  second_le : Sieve.MTMoments.secondMoment W ≤ (W.support.card : ℝ) * M2

/-- Build `MomentBounds W` from pointwise caps on `W.w` over `W.support`. -/
def bounds_of_pointwise
    (W : Sieve.MaynardWeights.Weight)
    (M  : ℝ) (hub  : ∀ n ∈ W.support, W.w n ≤ M)
    (M2 : ℝ) (hub2 : ∀ n ∈ W.support, (W.w n)^2 ≤ M2)
    : MomentBounds W :=
{ M := M,
  M2 := M2,
  first_le  := Sieve.MTMomentBounds.firstMoment_le_card_mul_bound W M hub,
  second_le := Sieve.MTMomentBounds.secondMoment_le_card_mul_bound_sq W M2 hub2 }

end Sieve.Stage2Weight
