/-
  Sieve/Analytic/LargeSieveDefs.lean
  Small readability helpers for large-sieve use:
  - `residueMass` = L² mass over residues for a fixed modulus `q`
  - Wrappers that restate toolbox inequalities in terms of `residueMass`
-/
import Mathlib
import Sieve.Analytic.LargeSieveCore
import Sieve.Analytic.LargeSieveConvenience

noncomputable section
open Classical BigOperators

namespace Sieve
namespace Analytic

/-- L² mass across residue classes for a fixed modulus `q`. -/
def residueMass (a : ℕ → ℂ) (N q : ℕ) : ℝ :=
  ∑ r : ZMod q.succ, ‖residueSum a N q r‖^2

@[simp] lemma residueMass_def (a : ℕ → ℂ) (N q : ℕ) :
    residueMass a N q = ∑ r : ZMod q.succ, ‖residueSum a N q r‖^2 := rfl

lemma residueMass_nonneg (a : ℕ → ℂ) (N q : ℕ) : 0 ≤ residueMass a N q := by
  classical
  unfold residueMass
  refine Finset.sum_nonneg ?h
  intro r _
  simpa using (sq_nonneg (‖residueSum a N q r‖ : ℝ))

/-- Toolbox large sieve, phrased with `residueMass` over `q ∈ range (Q+1)`. -/
theorem largeSieve_mass_over_range
    (T : BVToolbox) (a : ℕ → ℂ) {N Q : ℕ} (hN : 1 ≤ N) (hQ : 1 ≤ Q) :
    (∑ q ∈ Finset.range (Q + 1), residueMass a N q)
      ≤ T.C_ls * (N + Q^2) * (∑ n ∈ Finset.Icc 1 N, ‖a n‖^2) := by
  simpa [residueMass] using
    (T.largeSieve_residueProgressions a hN hQ)

/-- Clean subrange corollary using `residueMass` over `q ∈ [1, Q]`. -/
theorem largeSieve_mass_over_Icc1Q
    (T : BVToolbox) (a : ℕ → ℂ) {N Q : ℕ} (hN : 1 ≤ N) (hQ : 1 ≤ Q) :
    (∑ q ∈ Finset.Icc 1 Q, residueMass a N q)
      ≤ T.C_ls * (N + Q^2) * (∑ n ∈ Finset.Icc 1 N, ‖a n‖^2) := by
  -- Reuse the convenience lemma and unfold `residueMass`.
  simpa [residueMass] using
    (largeSieve_over_Icc1Q T a hN hQ)

end Analytic
end Sieve

