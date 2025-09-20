/-
  Sieve/MTMoments.lean
  Moments over a finite support (uses Weight.support and Weight.w).
-/
import Mathlib
import Sieve.MaynardWeights

noncomputable section
open Classical
open scoped BigOperators

namespace Sieve
namespace MTMoments

/-- First moment as a finite sum over the support. -/
def firstMoment (W : Sieve.MaynardWeights.Weight) : ℝ :=
  ∑ n ∈ W.support, W.w n

/-- Second moment as a finite sum over the support. -/
def secondMoment (W : Sieve.MaynardWeights.Weight) : ℝ :=
  ∑ n ∈ W.support, (W.w n)^2

@[simp] lemma firstMoment_sum_repr (W : Sieve.MaynardWeights.Weight) :
  firstMoment W = ∑ n ∈ W.support, W.w n := rfl

@[simp] lemma secondMoment_sum_repr (W : Sieve.MaynardWeights.Weight) :
  secondMoment W = ∑ n ∈ W.support, (W.w n)^2 := rfl

/-- If `w ≥ 0` on the support, the first moment is nonnegative. -/
lemma firstMoment_nonneg_of_nonneg
    (W : Sieve.MaynardWeights.Weight)
    (hnn : ∀ n ∈ W.support, 0 ≤ W.w n) :
    0 ≤ firstMoment W := by
  simpa [firstMoment] using
    Finset.sum_nonneg (by intro n hn; exact hnn n hn)

/-- The second moment is always nonnegative. -/
lemma secondMoment_nonneg (W : Sieve.MaynardWeights.Weight) :
    0 ≤ secondMoment W := by
  have : ∀ n ∈ W.support, 0 ≤ (W.w n)^2 := by
    intro n _; exact sq_nonneg _
  simpa [secondMoment] using
    Finset.sum_nonneg (by intro n hn; exact this n hn)

end MTMoments
end Sieve
