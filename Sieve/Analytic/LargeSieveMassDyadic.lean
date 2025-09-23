/-
  Sieve/Analytic/LargeSieveMassDyadic.lean
  Convenience: restate dyadic and weighted dyadic large-sieve bounds in terms
  of the per-modulus L² mass `residueMass`. Uses only lightweight algebraic steps.
-/
import Mathlib
import Sieve.Analytic.LargeSieveCore
import Sieve.Analytic.LargeSieveDefs

noncomputable section
open Classical BigOperators

namespace Sieve
namespace Analytic

/--
Dyadic large-sieve, phrased with `residueMass`:

  ∑_{q=Q₁}^{Q₂} residueMass a N q
    ≤ C_ls * (N + Q₂^2) * ∑_{n=1}^N ‖a n‖².
-/
theorem largeSieve_mass_over_IccQ1Q2
    (T : BVToolbox) (a : ℕ → ℂ) {N Q₁ Q₂ : ℕ}
    (hN : 1 ≤ N) (hQ12 : Q₁ ≤ Q₂) (hQ2 : 1 ≤ Q₂) :
    (∑ q ∈ Finset.Icc Q₁ Q₂, residueMass a N q)
      ≤ T.C_ls * (N + Q₂^2) * (∑ n ∈ Finset.Icc 1 N, ‖a n‖^2) := by
  simpa [residueMass] using
    (T.largeSieve_residueProgressions_dyadic a hN hQ12 hQ2)

/--
Weighted dyadic large-sieve, phrased with `residueMass`:

If `0 ≤ w q ≤ 1` for all `q`, then
  ∑_{q=Q₁}^{Q₂} w q * residueMass a N q
    ≤ C_ls * (N + Q₂^2) * ∑_{n=1}^N ‖a n‖².

Proof idea:
  Extend weights to `w' q = w q` on `[Q₁,Q₂]` and `0` elsewhere.
  Apply the toolbox weighted bound over `q ∈ range (Q₂+1)`,
  then use subset monotonicity with nonnegative summands.
-/
theorem largeSieve_weighted_mass_over_IccQ1Q2
    (T : BVToolbox) (a : ℕ → ℂ) (w : ℕ → ℝ) {N Q₁ Q₂ : ℕ}
    (hw : ∀ q, 0 ≤ w q ∧ w q ≤ 1)
    (hN : 1 ≤ N) (hQ12 : Q₁ ≤ Q₂) (hQ2 : 1 ≤ Q₂) :
    (∑ q ∈ Finset.Icc Q₁ Q₂, w q * residueMass a N q)
      ≤ T.C_ls * (N + Q₂^2) * (∑ n ∈ Finset.Icc 1 N, ‖a n‖^2) := by
  classical
  -- Extend weights outside the dyadic window by zero.
  let w' : ℕ → ℝ := fun q => if q ∈ Finset.Icc Q₁ Q₂ then w q else 0
  have hw' : ∀ q, 0 ≤ w' q ∧ w' q ≤ 1 := by
    intro q
    by_cases hq : q ∈ Finset.Icc Q₁ Q₂
    · have hq0 := hw q
      simpa [w', hq] using hq0
    · simp [w', hq, (show (0 : ℝ) ≤ 0 by norm_num)]
  -- Nonnegativity of the per-index summands we will use for subset monotonicity.
  let f : ℕ → ℝ := fun q => w' q * residueMass a N q
  have f_nonneg : ∀ q, 0 ≤ f q := by
    intro q
    have hw0 : 0 ≤ w' q := (hw' q).left
    have hm0 : 0 ≤ residueMass a N q := residueMass_nonneg a N q
    exact mul_nonneg hw0 hm0
  -- `[Q₁, Q₂] ⊆ range (Q₂+1)`.
  have hSubset : Finset.Icc Q₁ Q₂ ⊆ Finset.range (Q₂ + 1) := by
    intro q hq
    rcases Finset.mem_Icc.mp hq with ⟨_, hqQ2⟩
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le hqQ2)
  -- Identify `f` on the dyadic window: `w' = w` there.
  have f_on_window :
      ∀ {q}, q ∈ Finset.Icc Q₁ Q₂ → f q = w q * residueMass a N q := by
    intro q hq
    simp [f, w', hq]
  -- Sum over the window is ≤ sum over the range thanks to nonnegativity.
  have h_sub :
      (∑ q ∈ Finset.Icc Q₁ Q₂, f q)
        ≤ (∑ q ∈ Finset.range (Q₂ + 1), f q) :=
    Finset.sum_le_sum_of_subset_of_nonneg
      hSubset
      (by
        intro q _ _
        exact f_nonneg q)
  -- Left-hand side is exactly the weighted dyadic mass we want.
  have hL : (∑ q ∈ Finset.Icc Q₁ Q₂, f q)
            = (∑ q ∈ Finset.Icc Q₁ Q₂, w q * residueMass a N q) := by
    refine Finset.sum_congr rfl ?_
    intro q hq; simpa [f_on_window hq]
  -- Apply toolbox weighted large sieve on the larger index set with weights `w'`.
  have hRS :
      (∑ q ∈ Finset.range (Q₂ + 1), f q)
        ≤ T.C_ls * (N + Q₂^2) * (∑ n ∈ Finset.Icc 1 N, ‖a n‖^2) := by
    simpa [f, w', residueMass] using
      (T.largeSieve_residueProgressions_weighted a w' hw' hN hQ2)
  -- Conclude.
  exact (le_trans (by simpa [hL] using h_sub) hRS)

end Analytic
end Sieve

