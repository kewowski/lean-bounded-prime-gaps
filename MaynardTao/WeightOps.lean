import Mathlib
import MaynardTao.WeightsAPI

/-!
MaynardTao/WeightOps.lean
-------------------------
Basic operations on `SieveWeight` that preserve nonnegativity and a correct `support_spec`.

This module provides:
* `SieveWeight.restrict N` — restrict a weight to indices `n ≤ N` (zero elsewhere).
* A few small `@[simp]` lemmas describing the new support and values.
-/

namespace MaynardTao

namespace SieveWeight

variable {P : WeightParams}

private def restrictSupport (W : SieveWeight P) (N : ℕ) : Finset ℕ :=
  W.support.filter (fun n => n ≤ N)

private def restrictW (W : SieveWeight P) (N : ℕ) (n : ℕ) : ℚ :=
  if n ≤ N ∧ n ∈ W.support then W.w n else 0

/-- Restrict a weight to the range `n ≤ N`. Values outside are set to `0`.
The support becomes `W.support.filter (fun n => n ≤ N)`, and `support_spec` holds. -/
def restrict (W : SieveWeight P) (N : ℕ) : SieveWeight P :=
{ support := restrictSupport W N,
  w := restrictW W N,
  nonneg := by
    intro n
    classical
    by_cases h : n ≤ N ∧ n ∈ W.support
    · have := W.nonneg n
      simpa [restrictW, h]
    · simp [restrictW, h],
  support_spec := by
    classical
    intro n
    by_cases hle : n ≤ N
    · by_cases hmem : n ∈ W.support
      ·
        have hz : W.w n = 0 ↔ n ∉ W.support := W.support_spec n
        simp [restrictW, restrictSupport, hle, hmem, hz, Finset.mem_filter]
      ·
        simp [restrictW, restrictSupport, hle, hmem, Finset.mem_filter]
    ·
      simp [restrictW, restrictSupport, hle, Finset.mem_filter] }

section Simps

variable (W : SieveWeight P) (N : ℕ)

@[simp] lemma restrict_support :
    (W.restrict N).support = W.support.filter (fun n => n ≤ N) := rfl

@[simp] lemma restrict_w_of_le_of_mem {n : ℕ}
    (hnle : n ≤ N) (hnmem : n ∈ W.support) :
    (W.restrict N).w n = W.w n := by
  simp [restrict, restrictW, hnle, hnmem]

@[simp] lemma restrict_w_of_not_le {n : ℕ}
    (hnle : ¬ n ≤ N) :
    (W.restrict N).w n = 0 := by
  simp [restrict, restrictW, hnle]

@[simp] lemma restrict_w_of_le_of_not_mem {n : ℕ}
    (hnle : n ≤ N) (hnmem : n ∉ W.support) :
    (W.restrict N).w n = 0 := by
  simp [restrict, restrictW, hnle, hnmem]

end Simps

end SieveWeight

end MaynardTao
