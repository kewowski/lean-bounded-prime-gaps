import Mathlib
import MaynardTao.Sums
import MaynardTao.AdmissibleTuples

/-!
MaynardTao/ShiftPrimes.lean
---------------------------
Shifted-primality utilities built on the lightweight sums API.

* `shiftNat n h`   : interpret `n + h` as a natural by truncating negatives to 0.
* `primePred h`    : predicate `n ↦ Nat.Prime (shiftNat n h)`.
* `S_prime W N H`  : sum over `h ∈ H` of `S_of` with `primePred h` (noncomputable).
* `S_prime_nonneg` : nonnegativity of `S_prime`.
-/

namespace MaynardTao

open scoped BigOperators

/-- Coerce the integer `n + h` to `ℕ` by truncating negatives to `0`. -/
def shiftNat (n : ℕ) (h : ℤ) : ℕ :=
  Int.toNat ((n : ℤ) + h)

/-- The predicate "n + h is prime" (with negative shifted values mapped to `0`). -/
def primePred (h : ℤ) (n : ℕ) : Prop :=
  Nat.Prime (shiftNat n h)

namespace ShiftPrimes

variable {P : WeightParams}

/-- Sum over shifts `h ∈ H` of the weighted count of `n ≤ N` with `n + h` prime. -/
noncomputable def S_prime (W : SieveWeight P) (N : ℕ) (H : Finset ℤ) : ℚ := by
  classical
  exact ∑ h ∈ H, Sums.S_of (W := W) N (primePred h)

/-- Nonnegativity is immediate from nonnegativity of the summands. -/
lemma S_prime_nonneg (W : SieveWeight P) (N : ℕ) (H : Finset ℤ) :
    0 ≤ S_prime (W := W) N H := by
  classical
  unfold S_prime
  refine Finset.sum_nonneg ?_
  intro h hh
  exact Sums.S_of_nonneg (W := W) N (primePred h)

end ShiftPrimes

end MaynardTao
