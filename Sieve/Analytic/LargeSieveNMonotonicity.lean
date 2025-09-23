/-
  Sieve/Analytic/LargeSieveNMonotonicity.lean
  Monotonicity helpers in the window size `N` for large-sieve L² bounds.

  Goal: If you have a large-sieve bound stated at some `N`, you can *upgrade
  the RHS* to any larger `N' ≥ N` without touching Stage-2/3 callers. This is
  useful when rounding `N` upward to a cleaner expression.

  Results:
    • `largeSieve_over_range_upgrade_N`
    • `largeSieve_weighted_over_range_upgrade_N`
    • `largeSieve_dyadic_upgrade_N`
-/
import Mathlib
import Sieve.Analytic.LargeSieveCore
import Sieve.Analytic.DataMassBasics

noncomputable section
open Classical BigOperators

namespace Sieve
namespace Analytic

/-- Helper: `(N + Q^2) ≤ (N' + Q^2)` as reals when `N ≤ N'`. -/
private lemma add_sq_mono_in_N_real {N N' Q : ℕ} (hNN' : N ≤ N') :
    ((N + Q^2 : ℕ) : ℝ) ≤ ((N' + Q^2 : ℕ) : ℝ) := by
  have : N + Q^2 ≤ N' + Q^2 := Nat.add_le_add hNN' (Nat.le_refl _)
  exact_mod_cast this

/-- Nonnegativity: `0 ≤ C_ls` from `1 ≤ C_ls`. -/
private lemma C_ls_nonneg {T : BVToolbox} : 0 ≤ T.C_ls :=
  le_trans (by norm_num : (0 : ℝ) ≤ 1) T.C_ls_pos

/--
Upgrade the *range*-indexed large-sieve RHS from `N` to any `N' ≥ N`.

Consequence:
  ∑_{q=0}^Q ∑_{r} ‖S_N(q,r)‖²
    ≤ C_ls * (N' + Q^2) * ∑_{n=1}^{N'} ‖a n‖².
-/
theorem largeSieve_over_range_upgrade_N
    (T : BVToolbox) (a : ℕ → ℂ) {N N' Q : ℕ}
    (hN : 1 ≤ N) (hQ : 1 ≤ Q) (hNN' : N ≤ N') (hN' : 1 ≤ N') :
    (∑ q ∈ Finset.range (Q + 1),
       ∑ r : ZMod q.succ, ‖residueSum a N q r‖^2)
      ≤ T.C_ls * (N' + Q^2) * (∑ n ∈ Finset.Icc 1 N', ‖a n‖^2) := by
  -- Base bound at `N`.
  have h0 := T.largeSieve_residueProgressions a hN hQ
  -- Strengthen RHS: bump `(N + Q^2)` and the data mass from `N` to `N'`.
  have hMass_mono :
      (∑ n ∈ Finset.Icc 1 N, ‖a n‖^2)
        ≤ (∑ n ∈ Finset.Icc 1 N', ‖a n‖^2) :=
    dataL2_mono_in_N a hNN'
  have hMass_nonneg :
      0 ≤ (∑ n ∈ Finset.Icc 1 N, ‖a n‖^2) := dataL2_nonneg a N
  have hNterm : ((N + Q^2 : ℕ) : ℝ) ≤ ((N' + Q^2 : ℕ) : ℝ) :=
    add_sq_mono_in_N_real (Q := Q) hNN'
  -- First bump the `(N + Q^2)` factor.
  have step1 :
      T.C_ls * (N + Q^2) * (∑ n ∈ Finset.Icc 1 N, ‖a n‖^2)
        ≤ T.C_ls * (N' + Q^2) * (∑ n ∈ Finset.Icc 1 N, ‖a n‖^2) := by
    exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hNterm hMass_nonneg)
            (C_ls_nonneg)
  -- Then bump the mass from `N` to `N'`.
  have hC' : 0 ≤ T.C_ls * ((N' + Q^2 : ℕ) : ℝ) := by
    refine mul_nonneg (C_ls_nonneg) ?_
    exact_mod_cast (Nat.zero_le (N' + Q^2))
  have step2 :
      T.C_ls * (N' + Q^2) * (∑ n ∈ Finset.Icc 1 N, ‖a n‖^2)
        ≤ T.C_ls * (N' + Q^2) * (∑ n ∈ Finset.Icc 1 N', ‖a n‖^2) :=
    mul_le_mul_of_nonneg_left hMass_mono hC'
  -- Chain the upgrades on the RHS.
  exact le_trans h0 (le_trans step1 step2)

/--
Upgrade the *weighted* range-indexed large-sieve RHS from `N` to any `N' ≥ N`.

Consequence:
  ∑_{q=0}^Q w(q) ∑_{r} ‖S_N(q,r)‖²
    ≤ C_ls * (N' + Q^2) * ∑_{n=1}^{N'} ‖a n‖².
-/
theorem largeSieve_weighted_over_range_upgrade_N
    (T : BVToolbox) (a : ℕ → ℂ) (w : ℕ → ℝ) {N N' Q : ℕ}
    (hw : ∀ q, 0 ≤ w q ∧ w q ≤ 1)
    (hN : 1 ≤ N) (hQ : 1 ≤ Q) (hNN' : N ≤ N') (hN' : 1 ≤ N') :
    (∑ q ∈ Finset.range (Q + 1),
       w q * (∑ r : ZMod q.succ, ‖residueSum a N q r‖^2))
      ≤ T.C_ls * (N' + Q^2) * (∑ n ∈ Finset.Icc 1 N', ‖a n‖^2) := by
  -- Base weighted bound at `N`.
  have h0 := T.largeSieve_residueProgressions_weighted a w hw hN hQ
  -- Same RHS upgrade as in the unweighted case.
  have hMass_mono :
      (∑ n ∈ Finset.Icc 1 N, ‖a n‖^2)
        ≤ (∑ n ∈ Finset.Icc 1 N', ‖a n‖^2) :=
    dataL2_mono_in_N a hNN'
  have hMass_nonneg :
      0 ≤ (∑ n ∈ Finset.Icc 1 N, ‖a n‖^2) := dataL2_nonneg a N
  have hNterm : ((N + Q^2 : ℕ) : ℝ) ≤ ((N' + Q^2 : ℕ) : ℝ) :=
    add_sq_mono_in_N_real (Q := Q) hNN'
  have step1 :
      T.C_ls * (N + Q^2) * (∑ n ∈ Finset.Icc 1 N, ‖a n‖^2)
        ≤ T.C_ls * (N' + Q^2) * (∑ n ∈ Finset.Icc 1 N, ‖a n‖^2) := by
    exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hNterm hMass_nonneg)
            (C_ls_nonneg)
  have hC' : 0 ≤ T.C_ls * ((N' + Q^2 : ℕ) : ℝ) := by
    refine mul_nonneg (C_ls_nonneg) ?_
    exact_mod_cast (Nat.zero_le (N' + Q^2))
  have step2 :
      T.C_ls * (N' + Q^2) * (∑ n ∈ Finset.Icc 1 N, ‖a n‖^2)
        ≤ T.C_ls * (N' + Q^2) * (∑ n ∈ Finset.Icc 1 N', ‖a n‖^2) :=
    mul_le_mul_of_nonneg_left hMass_mono hC'
  exact le_trans h0 (le_trans step1 step2)

/--
Upgrade the *dyadic* large-sieve RHS from `N` to any `N' ≥ N`.

Consequence:
  ∑_{q=Q₁}^{Q₂} ∑_{r} ‖S_N(q,r)‖²
    ≤ C_ls * (N' + Q₂^2) * ∑_{n=1}^{N'} ‖a n‖².
-/
theorem largeSieve_dyadic_upgrade_N
    (T : BVToolbox) (a : ℕ → ℂ) {N N' Q₁ Q₂ : ℕ}
    (hN : 1 ≤ N) (hQ12 : Q₁ ≤ Q₂) (hQ2 : 1 ≤ Q₂) (hNN' : N ≤ N') (hN' : 1 ≤ N') :
    (∑ q ∈ Finset.Icc Q₁ Q₂,
       ∑ r : ZMod q.succ, ‖residueSum a N q r‖^2)
      ≤ T.C_ls * (N' + Q₂^2) * (∑ n ∈ Finset.Icc 1 N', ‖a n‖^2) := by
  -- Base dyadic bound at `N`.
  have h0 := T.largeSieve_residueProgressions_dyadic a hN hQ12 hQ2
  -- Upgrade RHS as before (with `Q` replaced by `Q₂`).
  have hMass_mono :
      (∑ n ∈ Finset.Icc 1 N, ‖a n‖^2)
        ≤ (∑ n ∈ Finset.Icc 1 N', ‖a n‖^2) :=
    dataL2_mono_in_N a hNN'
  have hMass_nonneg :
      0 ≤ (∑ n ∈ Finset.Icc 1 N, ‖a n‖^2) := dataL2_nonneg a N
  have hNterm : ((N + Q₂^2 : ℕ) : ℝ) ≤ ((N' + Q₂^2 : ℕ) : ℝ) :=
    add_sq_mono_in_N_real (Q := Q₂) hNN'
  have step1 :
      T.C_ls * (N + Q₂^2) * (∑ n ∈ Finset.Icc 1 N, ‖a n‖^2)
        ≤ T.C_ls * (N' + Q₂^2) * (∑ n ∈ Finset.Icc 1 N, ‖a n‖^2) := by
    exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hNterm hMass_nonneg)
            (C_ls_nonneg)
  have hC' : 0 ≤ T.C_ls * ((N' + Q₂^2 : ℕ) : ℝ) := by
    refine mul_nonneg (C_ls_nonneg) ?_
    exact_mod_cast (Nat.zero_le (N' + Q₂^2))
  have step2 :
      T.C_ls * (N' + Q₂^2) * (∑ n ∈ Finset.Icc 1 N, ‖a n‖^2)
        ≤ T.C_ls * (N' + Q₂^2) * (∑ n ∈ Finset.Icc 1 N', ‖a n‖^2) :=
    mul_le_mul_of_nonneg_left hMass_mono hC'
  exact le_trans h0 (le_trans step1 step2)

end Analytic
end Sieve

