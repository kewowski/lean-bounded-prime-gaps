/-
  Sieve/Analytic/DataMassBasics.lean
  Basic L¹ mass across residue classes: definition and nonnegativity.
-/
import Mathlib
import Sieve.Analytic.ResidueSumBasics

noncomputable section
open Classical BigOperators

namespace Sieve
namespace Analytic

/-- L¹ mass across residues for modulus `q`:
    `∑_{r mod q+1} ‖residueSum a N q r‖`. -/
def residueL1 (a : ℕ → ℂ) (N q : ℕ) : ℝ :=
  ∑ r : ZMod q.succ, ‖residueSum a N q r‖

@[simp] lemma residueL1_def (a : ℕ → ℂ) (N q : ℕ) :
    residueL1 a N q = ∑ r : ZMod q.succ, ‖residueSum a N q r‖ := rfl

/-- Nonnegativity of the L¹ mass across residues. -/
theorem residueL1_nonneg (a : ℕ → ℂ) (N q : ℕ) :
    0 ≤ residueL1 a N q := by
  classical
  -- Sum of nonnegative terms over a finite type is nonnegative.
  have h :
      0 ≤
        (∑ r ∈ (Finset.univ : Finset (ZMod q.succ)),
          ‖residueSum a N q r‖) := by
    refine Finset.sum_nonneg ?_
    intro r _; exact norm_nonneg _
  simpa [residueL1] using h

end Analytic
end Sieve
