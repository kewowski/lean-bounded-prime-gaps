import Mathlib
import MaynardTao.WeightsAPI

/-!
MaynardTao/WeightOps2.lean
--------------------------
Linear operations on `SieveWeight` that preserve:
* nonnegativity
* a correct `support_spec` (i.e. `w n = 0 ↔ n ∉ support`)

Provided:
* `SieveWeight.scale`  : scale by `c ≥ 0`, with `c ≠ 0`
* `SieveWeight.add`    : pointwise sum of two weights (same `P`)
-/

namespace MaynardTao
namespace SieveWeight

variable {P : WeightParams}

/-- Scale a weight by a nonnegative, nonzero scalar. -/
def scale (W : SieveWeight P) (c : ℚ) (hc0 : 0 ≤ c) (hcz : c ≠ 0) : SieveWeight P :=
{ support := W.support
, w := fun n => c * W.w n
, nonneg := by
    intro n
    exact mul_nonneg hc0 (W.nonneg n)
, support_spec := by
    intro n
    have hz : c * W.w n = 0 ↔ W.w n = 0 := by
      constructor
      · intro h
        have := mul_eq_zero.mp h
        rcases this with h0 | h0
        · exact (hcz h0).elim
        · exact h0
      · intro h
        simp [h]
    simpa [hz] using (W.support_spec n) }

/-- Pointwise sum of two weights (same `P`). -/
def add (W₁ W₂ : SieveWeight P) : SieveWeight P :=
let Wsum : ℕ → ℚ := fun n => W₁.w n + W₂.w n
let S := (W₁.support ∪ W₂.support).filter (fun n => Wsum n ≠ 0)
{ support := S
, w := Wsum
, nonneg := by
    intro n
    exact add_nonneg (W₁.nonneg n) (W₂.nonneg n)
, support_spec := by
    classical
    intro n
    -- We show: Wsum n = 0 ↔ n ∉ (union).filter (fun m => Wsum m ≠ 0)
    change (W₁.w n + W₂.w n = 0) ↔
      n ∉ (W₁.support ∪ W₂.support).filter (fun m => W₁.w m + W₂.w m ≠ 0)
    constructor
    · intro hz
      -- If the value is zero, the filter excludes it.
      simp [Finset.mem_filter, hz]
    · intro hnot
      by_cases hmem : n ∈ (W₁.support ∪ W₂.support)
      · -- In the union but not in the filter ⇒ value must be zero.
        have hnot' :
            ¬ ((n ∈ (W₁.support ∪ W₂.support)) ∧ (W₁.w n + W₂.w n ≠ 0)) := by
          simpa [Finset.mem_filter] using hnot
        have hnnz : ¬ (W₁.w n + W₂.w n ≠ 0) := by
          intro hne; exact hnot' ⟨hmem, hne⟩
        exact Classical.not_not.mp hnnz
      · -- Not in the union ⇒ not in either support ⇒ both components are zero.
        have hn₁ : n ∉ W₁.support := by
          intro h
          exact hmem (Finset.mem_union.mpr (Or.inl h))
        have hn₂ : n ∉ W₂.support := by
          intro h
          exact hmem (Finset.mem_union.mpr (Or.inr h))
        have hz₁ : W₁.w n = 0 := (W₁.support_spec n).mpr hn₁
        have hz₂ : W₂.w n = 0 := (W₂.support_spec n).mpr hn₂
        simp [hz₁, hz₂] }

end SieveWeight
end MaynardTao
