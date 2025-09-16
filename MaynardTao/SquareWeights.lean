import Mathlib
import MaynardTao.WeightsAPI
import MaynardTao.Sums

/-!
MaynardTao/SquareWeights.lean
-----------------------------
Generic square weights:

Given:
* a finite index set `I : Finset ι` with coefficients `lam : ι → ℚ`,
* predicates `φ i : ℕ → Prop` (decidable for each `i`),

define the quadratic form
  Q(n) = (∑ i ∈ I, lam i * indicator (φ i n))^2  (as a rational),
and build a `SieveWeight` supported on `n ≤ N` (zero outside), with:

* nonnegativity: by squaring
* `support_spec`: `w n = 0 ↔ n ∉ support` where support = `(range (N+1)).filter (w n ≠ 0)`.
-/

namespace MaynardTao
namespace SquareWeights

open scoped BigOperators

/-- Quadratic-form value at `n` from a coefficient family `lam`
    and predicates `φ`. -/
noncomputable def quadVal {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (lam : ι → ℚ) (φ : ι → ℕ → Prop)
    [∀ i, DecidablePred (φ i)]
    (n : ℕ) : ℚ :=
  (∑ i ∈ I, lam i * indicator (φ i n)) ^ 2

/-- Build a `SieveWeight` by restricting the quadratic form to `n ≤ N`
    (zero outside). The support records exactly the nonzeros within `≤ N`. -/
noncomputable def ofSquareFamilyOnRange
    {P : WeightParams} {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (lam : ι → ℚ) (φ : ι → ℕ → Prop)
    [∀ i, DecidablePred (φ i)]
    (N : ℕ) : SieveWeight P :=
by
  classical
  -- local definitions
  let Q : ℕ → ℚ := fun n => quadVal I lam φ n
  let w : ℕ → ℚ := fun n => if n ≤ N then Q n else 0
  let S : Finset ℕ := (Finset.range (N + 1)).filter (fun n => w n ≠ 0)
  refine
  { support := S
  , w := w
  , nonneg := ?nonneg
  , support_spec := ?spec } ;
  -- nonnegativity
  · intro n
    by_cases hle : n ≤ N
    ·
      have hsq : 0 ≤ (∑ i ∈ I, lam i * indicator (φ i n)) ^ 2 := by
        exact sq_nonneg _
      have hQ : 0 ≤ Q n := by simpa [Q, quadVal] using hsq
      simpa [w, hle] using hQ
    ·
      simp [w, hle]
  -- support_spec
  · intro n
    classical
    by_cases hle : n ≤ N
    ·
      have hmem_range : n ∈ Finset.range (N + 1) :=
        by exact Finset.mem_range.mpr (Nat.lt_succ_of_le hle)
      -- In-range: membership in S is exactly `w n ≠ 0`.
      have memS : n ∈ S ↔ w n ≠ 0 := by
        simpa [S, w, hle, hmem_range, Finset.mem_filter]
      -- Therefore `w n = 0 ↔ n ∉ S`.
      have notMemS : n ∉ S ↔ w n = 0 := by
        -- take `¬` of both sides in `memS`
        have := memS
        have := Iff.not this
        -- `¬ (w n ≠ 0)` is `w n = 0` (classical)
        simpa [not_not] using this
      exact notMemS.symm
    ·
      -- Outside the bound: `w n = 0` and not in the range, hence not in `S`.
      -- `simp` can compute both sides directly.
      simp [S, w, hle, Finset.mem_range, Nat.lt_succ_iff]

end SquareWeights
end MaynardTao
