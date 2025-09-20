/-
  Sieve/Stage3DensityBounds.lean
  Basic density bounds in Stage 3.
-/
import Mathlib
import Sieve.MTCore

noncomputable section
open Classical BigOperators

namespace Sieve
namespace Stage3

/-- Heavy density is always ≤ 1 when the support is nonempty. -/
theorem heavyDensity_le_one
    (W : Sieve.MaynardWeights.Weight) (τ : ℝ)
    (hpos : 0 < W.support.card) :
    Sieve.MTCore.heavyDensity W τ ≤ 1 := by
  classical
  set s  : Finset ℤ := W.support
  set P  : ℤ → Prop := fun n => τ ≤ W.w n
  set A  : Finset ℤ := s.filter P
  -- Pointwise: indicator ≤ 1 on s
  have hpt : ∀ n ∈ s, (if P n then (1 : ℝ) else 0) ≤ 1 := by
    intro n hn; by_cases hp : P n <;> simp [hp, zero_le_one]
  -- Sum over s gives: (A.card : ℝ) ≤ (s.card : ℝ)
  have hsum :
      (∑ n ∈ s, (if P n then (1 : ℝ) else 0))
        ≤ (∑ _n ∈ s, (1 : ℝ)) :=
    Finset.sum_le_sum (by intro n hn; exact hpt n hn)
  have hcard_le : (A.card : ℝ) ≤ (s.card : ℝ) := by
    -- normalize both sides
    have hleft :=
      (Finset.sum_filter (s := s) (p := P) (f := fun _ => (1 : ℝ))).symm
    simp [Finset.sum_const, nsmul_eq_mul] at hleft
    simpa [hleft, Finset.sum_const, nsmul_eq_mul] using hsum
  -- divide by |s| > 0
  have hscard_pos : 0 < (s.card : ℝ) := by exact_mod_cast hpos
  have : (A.card : ℝ) / (s.card : ℝ) ≤ 1 := by
    -- (A.card)/|s| ≤ (s.card)/|s| = 1
    have := div_le_div_of_nonneg_right hcard_le (le_of_lt hscard_pos)
    simpa [div_self (ne_of_gt hscard_pos)] using this
  simpa [Sieve.MTCore.heavyDensity, s, A] using this

end Stage3
end Sieve

