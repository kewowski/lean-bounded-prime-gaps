/-
  Sieve/MTMomentBounds.lean
  Specialized first-moment bound for Sieve.MaynardWeights.Weight.
-/
import Mathlib
import Sieve.MaynardWeights
import Sieve.MTMoments
import Sieve.SumBounds

noncomputable section
open Classical

namespace Sieve.MTMomentBounds

/-- If `W.w n ≤ M` for all `n ∈ W.support`, then
    `firstMoment W ≤ (W.support.card : ℝ) * M`. -/
lemma firstMoment_le_card_mul_bound
    (W : Sieve.MaynardWeights.Weight) (M : ℝ)
    (hub : ∀ n ∈ W.support, W.w n ≤ M) :
    Sieve.MTMoments.firstMoment W ≤ (W.support.card : ℝ) * M := by
  -- apply the generic finite-sum bound to `∑ n ∈ support, w n`
  simpa [Sieve.MTMoments.firstMoment] using
    Sieve.SumBounds.sum_le_card_mul_bound (s := W.support) (f := W.w) (M := M) hub

end Sieve.MTMomentBounds
/-
  Extra: second-moment bound from a pointwise square cap.
-/
namespace Sieve.MTMomentBounds

/-- If `(W.w n)^2 ≤ M2` for all `n ∈ W.support`, then
    `secondMoment W ≤ (W.support.card : ℝ) * M2`. -/
lemma secondMoment_le_card_mul_bound_sq
    (W : Sieve.MaynardWeights.Weight) (M2 : ℝ)
    (hub2 : ∀ n ∈ W.support, (W.w n)^2 ≤ M2) :
    Sieve.MTMoments.secondMoment W ≤ (W.support.card : ℝ) * M2 := by
  -- apply the generic finite-sum bound to `∑ n ∈ support, (w n)^2`
  simpa [Sieve.MTMoments.secondMoment] using
    Sieve.SumBounds.sum_le_card_mul_bound
      (s := W.support) (f := fun n => (W.w n)^2) (M := M2)
      (hub := hub2)

end Sieve.MTMomentBounds
