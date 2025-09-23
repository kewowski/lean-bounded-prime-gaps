/-
  Sieve/Analytic/L1Averages.lean
  Average L¹ mass across residue classes.

  Note:
  We keep this file minimal (definition + nonnegativity) to stay green.
  A sharper bound `residueL1Avg a N q ≤ ∑_{n=1}^N ‖a n‖` will be added later,
  once we settle on the preferred algebraic lemmas for dividing inequalities.
-/
import Mathlib
import Sieve.Analytic.ResidueSumBasics
import Sieve.Analytic.DataMassBasics

noncomputable section
open Classical BigOperators

namespace Sieve
namespace Analytic

/-- Average L¹ mass across residue classes for modulus `q`:
    `(1/(q+1)) * ∑_{r mod q+1} ‖residueSum a N q r‖`. -/
def residueL1Avg (a : ℕ → ℂ) (N q : ℕ) : ℝ :=
  residueL1 a N q / ((q.succ : ℕ) : ℝ)

@[simp] lemma residueL1Avg_def (a : ℕ → ℂ) (N q : ℕ) :
    residueL1Avg a N q = residueL1 a N q / ((q.succ : ℕ) : ℝ) := rfl

/-- Nonnegativity of the average L¹ mass. -/
theorem residueL1Avg_nonneg (a : ℕ → ℂ) (N q : ℕ) :
    0 ≤ residueL1Avg a N q := by
  classical
  have h₁ : 0 ≤ residueL1 a N q := residueL1_nonneg a N q
  have h₂ : 0 ≤ ((q.succ : ℕ) : ℝ) := by exact_mod_cast (Nat.zero_le (q.succ))
  simpa [residueL1Avg] using div_nonneg h₁ h₂

end Analytic
end Sieve
