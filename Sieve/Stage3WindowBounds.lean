/-
  Sieve/Stage3WindowBounds.lean
  Basic bounds for window hit counts (nonnegativity and |H|-upper bound).
-/
import Mathlib
import Sieve.Stage3PrimeFacade  -- windowHitCount / hitIndicator / windowSum

noncomputable section
open Classical BigOperators

namespace Sieve
namespace Stage3

/-- Window hit counts are nonnegative. -/
theorem windowHitCount_nonneg (H : Finset ℤ) (HS : HitSystem) (n : ℤ) :
    0 ≤ windowHitCount H HS n := by
  classical
  unfold windowHitCount windowSum hitIndicator
  refine Finset.sum_nonneg ?term
  intro h hh
  by_cases hp : HS.isHit (n + h)
  · simp [hp]
  · simp [hp]

/-- Window hit counts are bounded above by the window size `|H|`. -/
theorem windowHitCount_le_card (H : Finset ℤ) (HS : HitSystem) (n : ℤ) :
    windowHitCount H HS n ≤ (H.card : ℝ) := by
  classical
  unfold windowHitCount windowSum hitIndicator
  -- Each summand ≤ 1, so the sum ≤ |H| * 1 = |H|.
  have hpt :
      ∀ h ∈ H, (if HS.isHit (n + h) then (1 : ℝ) else 0) ≤ 1 := by
    intro h hh
    by_cases hp : HS.isHit (n + h)
    · simp [hp]
    · simp [hp, zero_le_one]
  have hsum :
      (∑ h ∈ H, (if HS.isHit (n + h) then (1 : ℝ) else 0))
        ≤ (∑ _h ∈ H, (1 : ℝ)) :=
    Finset.sum_le_sum (by intro h hh; exact hpt h hh)
  simpa [Finset.sum_const, nsmul_eq_mul, mul_comm] using hsum

end Stage3
end Sieve
