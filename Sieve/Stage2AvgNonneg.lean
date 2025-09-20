/-
  Sieve/Stage2AvgNonneg.lean
  The average weight on the support is nonnegative.
-/
import Mathlib
import Sieve.MaynardWeights
import Sieve.MTMoments

noncomputable section
open Classical
open scoped BigOperators

namespace Sieve.Stage2

/-- The average of `W.w` over its support is nonnegative. -/
lemma avg_nonneg (W : Sieve.MaynardWeights.Weight) :
    0 ≤ (∑ n ∈ W.support, W.w n) / (W.support.card : ℝ) := by
  classical
  have hsum_nonneg : 0 ≤ ∑ n ∈ W.support, W.w n := by
    refine Finset.sum_nonneg ?_
    intro n hn
    exact W.nonneg n
  have hden_nonneg : 0 ≤ (W.support.card : ℝ) := by
    exact_mod_cast (Nat.zero_le _)
  exact div_nonneg hsum_nonneg hden_nonneg

end Sieve.Stage2
