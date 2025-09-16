import Mathlib
import MaynardTao.WeightsAPI
import MaynardTao.AdmissibleTuples

/-!
MaynardTao/WeightBuilders.lean
------------------------------
Simple constructors for `SieveWeight` and a trivial `WeightParams`.

* `SieveWeight.ofSupport` builds a nonnegative weight equal to a constant `c` on a
  chosen finite support `S : Finset ℕ` and `0` elsewhere, with a clean `support_spec`.
* `trivialParams` provides an admissible, empty-tuple parameter pack.
-/

namespace MaynardTao

namespace SieveWeight

variable {P : WeightParams}

/-- Build a constant weight with value `c` on `S` and `0` elsewhere.
Requires `0 ≤ c` and `c ≠ 0` so that `support_spec` simplifies to
`w n = 0 ↔ n ∉ S`. -/
def ofSupport (S : Finset ℕ) (c : ℚ) (hc0 : 0 ≤ c) (hcz : c ≠ 0) : SieveWeight P :=
{ support := S,
  w := fun n => if n ∈ S then c else 0,
  nonneg := by
    intro n
    by_cases h : n ∈ S
    · simp [h, hc0]
    · simp [h],
  support_spec := by
    intro n
    by_cases h : n ∈ S
    · -- On-support: `w n = c ≠ 0` and `n ∉ S` is false.
      simp [h, hcz]
    · -- Off-support: value is `0` and `n ∉ S`.
      simp [h] }

end SieveWeight

/-- Trivial parameters: empty admissible tuple, `k = 0`. -/
def trivialParams : WeightParams where
  H := (∅ : Finset ℤ)
  k := 0
  admissible := Admissible.isAdmissible_empty

end MaynardTao
