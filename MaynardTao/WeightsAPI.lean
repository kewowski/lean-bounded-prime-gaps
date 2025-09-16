import Mathlib
import MaynardTao.AdmissibleTuples

/-!
MaynardTao/WeightsAPI.lean
--------------------------
A minimal, ASCII-only interface for Maynard–Tao style sieve weights.

* `WeightParams` packages the tuple `H`, its size `k`, and admissibility proof.
* `SieveWeight P` is a concrete weight with finite support on `ℕ` and nonnegativity.
* `total` and `average` are basic finite-support aggregations.
No `sorry`.
-/

namespace MaynardTao

open scoped BigOperators

/-- Parameters for the weight construction: an admissible finite set `H : Finset ℤ`
and its size `k`. -/
structure WeightParams where
  H : Finset ℤ
  k : ℕ
  admissible : isAdmissible H

/-- A sieve weight attached to parameters `P`. We keep it very abstract:
* `support : Finset ℕ` where the weight is potentially nonzero
* `w : ℕ → ℚ` the actual weight function
* `nonneg : ∀ n, 0 ≤ w n`
* `support_spec : w n = 0 ↔ n ∉ support` (so the support captures all nonzeros)
-/
structure SieveWeight (P : WeightParams) where
  support : Finset ℕ
  w : ℕ → ℚ
  nonneg : ∀ n, 0 ≤ w n
  support_spec : ∀ n, w n = 0 ↔ n ∉ support

namespace SieveWeight

variable {P : WeightParams} (W : SieveWeight P)

/-- Finite-support sum of the weights. -/
def total : ℚ := ∑ n ∈ W.support, W.w n

/-- Average value over the finite support. Returns `0` if `support.card = 0`. -/
def average : ℚ :=
  if _h : W.support.card ≠ 0 then
    (∑ n ∈ W.support, W.w n) / (W.support.card : ℚ)
  else
    0

end SieveWeight

/-- Shifting an admissible tuple preserves admissibility.
Re-export from `AdmissibleTuples` for convenience. -/
lemma admissible_translate_iff (H : Finset ℤ) (t : ℤ) :
    isAdmissible (translate H t) ↔ isAdmissible H :=
  Admissible.isAdmissible_translate_iff H t

end MaynardTao
