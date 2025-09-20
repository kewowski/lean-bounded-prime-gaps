/-
  Sieve/Stage3WindowMono.lean
  Monotonicity: enlarging the window H can only increase the hit count.
-/
import Mathlib
import Sieve.Stage3PrimeFacade  -- windowHitCount / hitIndicator / windowSum

noncomputable section
open Classical BigOperators

namespace Sieve
namespace Stage3

/-- If `H ⊆ H'`, the window hit count at `n` is monotone (nondecreasing). -/
theorem windowHitCount_mono_in_H
    {H H' : Finset ℤ} (HS : HitSystem) (n : ℤ) (hsub : H ⊆ H') :
    windowHitCount H HS n ≤ windowHitCount H' HS n := by
  classical
  -- Expand sums and apply `sum_le_sum_of_subset_of_nonneg`
  unfold windowHitCount windowSum hitIndicator
  have hnn :
      ∀ h ∈ H', h ∉ H → 0 ≤ (if HS.isHit (n + h) then (1 : ℝ) else 0) := by
    intro h hh' hnot
    by_cases hp : HS.isHit (n + h)
    · simp [hp]
    · simp [hp]
  -- Now apply the monotonicity lemma on sums over a subset.
  exact Finset.sum_le_sum_of_subset_of_nonneg (f := fun h => if HS.isHit (n + h) then (1 : ℝ) else 0)
    hsub hnn

end Stage3
end Sieve
