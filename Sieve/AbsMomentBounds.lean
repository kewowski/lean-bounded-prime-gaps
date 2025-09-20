/-
  Sieve/AbsMomentBounds.lean
  Absolute-value variant: if |w n| ≤ M (M ≥ 0) on the support,
  then secondMoment ≤ (#support) · M^2.
-/
import Mathlib
import Sieve.MaynardWeights
import Sieve.MTMoments
import Sieve.MTMomentBounds

noncomputable section
open Classical

namespace Sieve.MTMomentBounds

/-- If `0 ≤ M` and `|W.w n| ≤ M` for all `n ∈ W.support`, then
    `secondMoment W ≤ (W.support.card : ℝ) * M^2`. -/
lemma secondMoment_le_card_mul_abs_bound_sq
    (W : Sieve.MaynardWeights.Weight) (M : ℝ)
    (hM : 0 ≤ M)
    (habs : ∀ n ∈ W.support, |W.w n| ≤ M) :
    Sieve.MTMoments.secondMoment W ≤ (W.support.card : ℝ) * M^2 := by
  -- Turn the abs-bound into a square bound.
  have hub2 : ∀ n ∈ W.support, (W.w n)^2 ≤ M^2 := by
    intro n hn
    have h := habs n hn
    have h' : |W.w n| ≤ |M| := by simpa [abs_of_nonneg hM] using h
    -- Using `sq_le_sq`: a^2 ≤ b^2 ↔ |a| ≤ |b|.
    simpa using (sq_le_sq.mpr h')
  -- Apply the generic second-moment square-cap bound.
  simpa using
    Sieve.MTMomentBounds.secondMoment_le_card_mul_bound_sq W (M2 := M^2) hub2

end Sieve.MTMomentBounds
