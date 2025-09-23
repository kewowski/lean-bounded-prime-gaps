/-
  Sieve/Analytic/ResidueIndicator.lean
  Clean wrappers for residue-class indicators + toolbox orthogonality.
  No `simpa`; explicit rewrites and `simp` only where needed.
-/
import Mathlib
import Sieve.Analytic.LargeSieveCore

noncomputable section
open Classical BigOperators

namespace Sieve
namespace Analytic

/-- Indicator of the residue class of `n (mod q+1)` as a function on `ZMod (q+1)`. -/
def residueIndicator (q n : ℕ) : ZMod q.succ → ℝ :=
  fun r => if ((n : ZMod q.succ) = r) then (1 : ℝ) else 0

@[simp] lemma residueIndicator_apply (q n : ℕ) (r : ZMod q.succ) :
    residueIndicator q n r = (if ((n : ZMod q.succ) = r) then (1 : ℝ) else 0) := rfl

/-- Orthogonality of residue-indicator vectors, expressed via `residueIndicator`. -/
theorem residueIndicator_orthogonality
    (T : BVToolbox) {q n m : ℕ} :
    (∑ r : ZMod q.succ, residueIndicator q n r * residueIndicator q m r)
    = (if ((n : ZMod q.succ) = (m : ZMod q.succ)) then (1 : ℝ) else 0) := by
  change
    (∑ r : ZMod q.succ,
        (if ((n : ZMod q.succ) = r) then (1 : ℝ) else 0)
      * (if ((m : ZMod q.succ) = r) then (1 : ℝ) else 0))
    = (if ((n : ZMod q.succ) = (m : ZMod q.succ)) then (1 : ℝ) else 0)
  exact T.orthogonality_residueIndicators (q := q) (n := n) (m := m)

/--
Summing the indicator over all residues gives `1`.
Idea: use orthogonality with `m = n` and pointwise idempotence.
-/
theorem sum_residueIndicator_eq_one
    (T : BVToolbox) {q n : ℕ} :
    (∑ r : ZMod q.succ, residueIndicator q n r) = 1 := by
  classical
  -- Orthogonality with `m = n` (explicit `if`-form), then simplify RHS to `1`.
  have h₁ :
      (∑ r : ZMod q.succ,
          (if ((n : ZMod q.succ) = r) then (1 : ℝ) else 0)
        * (if ((n : ZMod q.succ) = r) then (1 : ℝ) else 0)) = 1 := by
    have h := T.orthogonality_residueIndicators (q := q) (n := n) (m := n)
    -- RHS reduces because `(n : ZMod _) = (n : ZMod _)`.
    simpa using h
  -- Idempotence on each summand: `(if p then 1 else 0)^2 = (if p then 1 else 0)`.
  have hIdem :
      (∑ r : ZMod q.succ,
          (if ((n : ZMod q.succ) = r) then (1 : ℝ) else 0)
        * (if ((n : ZMod q.succ) = r) then (1 : ℝ) else 0))
      =
      (∑ r : ZMod q.succ,
          (if ((n : ZMod q.succ) = r) then (1 : ℝ) else 0)) := by
    refine Finset.sum_congr rfl ?_
    intro r _
    by_cases hr : ((n : ZMod q.succ) = r)
    · simp [hr]
    · simp [hr]
  -- Rewrite the goal into the explicit `if`-form and close using `h₁` via `hIdem`.
  change
    (∑ r : ZMod q.succ,
        (if ((n : ZMod q.succ) = r) then (1 : ℝ) else 0)) = 1
  exact hIdem ▸ h₁

end Analytic
end Sieve
