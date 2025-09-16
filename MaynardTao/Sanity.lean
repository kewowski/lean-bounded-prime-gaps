import Mathlib
import MaynardTao.Inequalities
import MaynardTao.Sandwich
import MaynardTao.BoundedGaps
import MaynardTao.Sums

/-!
MaynardTao/Sanity.lean
----------------------
Edge-case checks:
* `r = 0` (both raw and Spec versions)
* `H = ∅` gives `S' = 0` and matches the right-hand bound
-/

namespace MaynardTao
namespace Sanity

open scoped BigOperators
variable {P : WeightParams}

/-- For any `W, N, H`, the `r = 0` case of the global inequality holds. -/
theorem r_zero_ok (W : SieveWeight P) (N : ℕ) (H : Finset ℤ) :
  Inequalities.RCrit (W := W) N H 0 :=
  Inequalities.RCrit_zero (W := W) N H

/-- Spec-version of the `r = 0` case. -/
theorem r_zero_ok_spec (s : BoundedGaps.Spec) :
  Inequalities.RCritSpec s 0 :=
  Inequalities.RCritSpec_zero s

/-- With `H = ∅`, the prime-shift sum is exactly zero. -/
@[simp] lemma S_prime_empty (W : SieveWeight P) (N : ℕ) :
  ShiftPrimes.S_prime (W := W) N (∅ : Finset ℤ) = 0 := by
  classical
  unfold ShiftPrimes.S_prime Sums.S_of
  simp

/-- Right bound matches the zero value when `H = ∅`. -/
lemma right_bound_empty (W : SieveWeight P) (N : ℕ) :
  ShiftPrimes.S_prime (W := W) N (∅ : Finset ℤ)
    ≤ (0 : ℚ) * Sums.S0 (W := W) N := by
  classical
  simpa [S_prime_empty, Finset.card_empty] using
    Inequalities.S_prime_le_cardH_S0 (W := W) N (∅ : Finset ℤ)

end Sanity
end MaynardTao
