import Mathlib
import MaynardTao.ShiftPrimes
import MaynardTao.Sums
import MaynardTao.WeightsAPI

/-!
MaynardTao/PrimeCounts.lean
---------------------------
Count how many of the shifts `n + h` (for `h ∈ H`) are prime, and build a
weighted sum for the predicate “at least r primes among the shifts”.

* `PrimeCounts.count H n`      : number of `h ∈ H` with `Nat.Prime (shiftNat n h)`
* `PrimeCounts.atLeast H r n`  : the proposition `r ≤ count H n`
* `PrimeCounts.S_atLeast W N H r` : weighted sum of the indicator of `atLeast H r`
* `S_atLeast_nonneg`           : nonnegativity of that sum
-/

namespace MaynardTao
namespace PrimeCounts

open scoped BigOperators

/-- For fixed `n`, count the shifts `h ∈ H` such that `n + h` is prime.
We use a `filter` and take the `card`. -/
noncomputable def count (H : Finset ℤ) (n : ℕ) : ℕ := by
  classical
  exact (H.filter (fun h => primePred h n)).card

@[simp] lemma count_empty (n : ℕ) : count (∅ : Finset ℤ) n = 0 := by
  classical
  simp [count]

/-- The predicate: at least `r` primes among the shifts indexed by `H`. -/
def atLeast (H : Finset ℤ) (r : ℕ) (n : ℕ) : Prop :=
  r ≤ count H n

variable {P : WeightParams}

/-- Weighted sum of the indicator of `atLeast H r`. -/
noncomputable def S_atLeast (W : SieveWeight P) (N : ℕ)
    (H : Finset ℤ) (r : ℕ) : ℚ :=
  Sums.S_of (W := W) N (fun n => atLeast H r n)

/-- Nonnegativity of `S_atLeast`. -/
lemma S_atLeast_nonneg (W : SieveWeight P) (N : ℕ)
    (H : Finset ℤ) (r : ℕ) : 0 ≤ S_atLeast (W := W) N H r := by
  classical
  unfold S_atLeast
  exact Sums.S_of_nonneg (W := W) N (fun n => atLeast H r n)

end PrimeCounts
end MaynardTao
