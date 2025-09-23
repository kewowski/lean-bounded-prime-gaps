/-
  Sieve/Analytic/LargeSieveMonotonicity.lean
  Monotonicity helpers for large-sieve RHS constants in `Q` / `Q₂`.

  Purpose:
    Allow upgrading any L² bound stated at ceiling `Q` (or `Q₂`) to a
    slightly looser bound with a larger ceiling `Q' ≥ Q` (or `Q₂' ≥ Q₂`),
    without touching Stage-2/3 callers.

  Results (all lightweight, algebraic proofs):
    • `largeSieve_over_range_upgrade_Q`
    • `largeSieve_over_Icc1Q_upgrade_Q`
    • `largeSieve_weighted_over_range_upgrade_Q`
    • `largeSieve_weighted_over_Icc1Q_upgrade_Q`
    • `largeSieve_dyadic_upgrade_Q2`
-/
import Mathlib
import Sieve.Analytic.LargeSieveCore
import Sieve.Analytic.LargeSieveConvenience

noncomputable section
open Classical BigOperators

namespace Sieve
namespace Analytic

/-- Helper: `(N + Q^2) ≤ (N + Q'^2)` as reals when `Q ≤ Q'`. -/
private lemma add_sq_mono_in_Q_real {N Q Q' : ℕ} (hQQ' : Q ≤ Q') :
    ((N + Q^2 : ℕ) : ℝ) ≤ ((N + Q'^2 : ℕ) : ℝ) := by
  have hmul : Q * Q ≤ Q' * Q' := Nat.mul_le_mul hQQ' hQQ'
  have hnat : N + Q * Q ≤ N + Q' * Q' := Nat.add_le_add (Nat.le_refl _) hmul
  simpa [pow_two] using (Nat.cast_le.mpr hnat)

/-- Nonnegativity: `0 ≤ ∑_{n=1}^N ‖a n‖²`. -/
private lemma dataMass_nonneg (a : ℕ → ℂ) (N : ℕ) :
    0 ≤ (∑ n ∈ Finset.Icc 1 N, ‖a n‖^2) := by
  classical
  refine Finset.sum_nonneg ?h
  intro n _; simpa using (sq_nonneg (‖a n‖ : ℝ))

/-- Nonnegativity: `0 ≤ C_ls` from `1 ≤ C_ls`. -/
private lemma C_ls_nonneg {T : BVToolbox} : 0 ≤ T.C_ls :=
  le_trans (by norm_num : (0 : ℝ) ≤ 1) T.C_ls_pos

/--
Upgrade the *range*-indexed large-sieve RHS from `Q` to any `Q' ≥ Q`.
-/
theorem largeSieve_over_range_upgrade_Q
    (T : BVToolbox) (a : ℕ → ℂ) {N Q Q' : ℕ}
    (hN : 1 ≤ N) (hQ : 1 ≤ Q) (hQQ' : Q ≤ Q') :
    (∑ q ∈ Finset.range (Q + 1),
       ∑ r : ZMod q.succ, ‖residueSum a N q r‖^2)
      ≤ T.C_ls * (N + Q'^2) * (∑ n ∈ Finset.Icc 1 N, ‖a n‖^2) := by
  -- Base bound at `Q`.
  have h0 := T.largeSieve_residueProgressions a hN hQ
  -- Strengthen RHS by bumping `Q` to `Q'`.
  have hMass := dataMass_nonneg a N
  have hStep :
      T.C_ls * (N + Q^2) * (∑ n ∈ Finset.Icc 1 N, ‖a n‖^2)
        ≤ T.C_ls * (N + Q'^2) * (∑ n ∈ Finset.Icc 1 N, ‖a n‖^2) := by
    have hMid : ((N + Q^2 : ℕ) : ℝ) ≤ ((N + Q'^2 : ℕ) : ℝ) :=
      add_sq_mono_in_Q_real hQQ'
    exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hMid hMass)
            (C_ls_nonneg)
  exact le_trans h0 hStep

/--
Upgrade the `q ∈ [1, Q]` large-sieve RHS to any `Q' ≥ Q`.
-/
theorem largeSieve_over_Icc1Q_upgrade_Q
    (T : BVToolbox) (a : ℕ → ℂ) {N Q Q' : ℕ}
    (hN : 1 ≤ N) (hQ : 1 ≤ Q) (hQQ' : Q ≤ Q') :
    (∑ q ∈ Finset.Icc 1 Q,
       ∑ r : ZMod q.succ, ‖residueSum a N q r‖^2)
      ≤ T.C_ls * (N + Q'^2) * (∑ n ∈ Finset.Icc 1 N, ‖a n‖^2) := by
  -- Base bound over `[1, Q]`.
  have h0 := largeSieve_over_Icc1Q T a hN hQ
  -- Strengthen RHS by bumping `Q` to `Q'`.
  have hMass := dataMass_nonneg a N
  have hStep :
      T.C_ls * (N + Q^2) * (∑ n ∈ Finset.Icc 1 N, ‖a n‖^2)
        ≤ T.C_ls * (N + Q'^2) * (∑ n ∈ Finset.Icc 1 N, ‖a n‖^2) := by
    have hMid : ((N + Q^2 : ℕ) : ℝ) ≤ ((N + Q'^2 : ℕ) : ℝ) :=
      add_sq_mono_in_Q_real hQQ'
    exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hMid hMass)
            (C_ls_nonneg)
  exact le_trans h0 hStep

/--
Upgrade the *weighted* range-indexed large-sieve RHS from `Q` to any `Q' ≥ Q`.
-/
theorem largeSieve_weighted_over_range_upgrade_Q
    (T : BVToolbox) (a : ℕ → ℂ) (w : ℕ → ℝ) {N Q Q' : ℕ}
    (hw : ∀ q, 0 ≤ w q ∧ w q ≤ 1)
    (hN : 1 ≤ N) (hQ : 1 ≤ Q) (hQQ' : Q ≤ Q') :
    (∑ q ∈ Finset.range (Q + 1),
       w q * (∑ r : ZMod q.succ, ‖residueSum a N q r‖^2))
      ≤ T.C_ls * (N + Q'^2) * (∑ n ∈ Finset.Icc 1 N, ‖a n‖^2) := by
  -- Base weighted bound at `Q`.
  have h0 := T.largeSieve_residueProgressions_weighted a w hw hN hQ
  -- Strengthen RHS by bumping `Q` to `Q'`.
  have hMass := dataMass_nonneg a N
  have hStep :
      T.C_ls * (N + Q^2) * (∑ n ∈ Finset.Icc 1 N, ‖a n‖^2)
        ≤ T.C_ls * (N + Q'^2) * (∑ n ∈ Finset.Icc 1 N, ‖a n‖^2) := by
    have hMid : ((N + Q^2 : ℕ) : ℝ) ≤ ((N + Q'^2 : ℕ) : ℝ) :=
      add_sq_mono_in_Q_real hQQ'
    exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hMid hMass)
            (C_ls_nonneg)
  exact le_trans h0 hStep

/--
Upgrade the *weighted* `q ∈ [1, Q]` large-sieve RHS to any `Q' ≥ Q`.
-/
theorem largeSieve_weighted_over_Icc1Q_upgrade_Q
    (T : BVToolbox) (a : ℕ → ℂ) (w : ℕ → ℝ) {N Q Q' : ℕ}
    (hw : ∀ q, 0 ≤ w q ∧ w q ≤ 1)
    (hN : 1 ≤ N) (hQ : 1 ≤ Q) (hQQ' : Q ≤ Q') :
    (∑ q ∈ Finset.Icc 1 Q,
       w q * (∑ r : ZMod q.succ, ‖residueSum a N q r‖^2))
      ≤ T.C_ls * (N + Q'^2) * (∑ n ∈ Finset.Icc 1 N, ‖a n‖^2) := by
  -- From the range-version monotonicity, just weaken the index set `[1,Q] ⊆ range(Q+1)`.
  -- First apply the base convenience bound at `Q`, then bump `Q → Q'`.
  have base :=
    (by
      -- convenience over `[1,Q]`
      simpa using
        (T.largeSieve_residueProgressions_weighted a w hw hN hQ))
  -- Now strengthen the RHS (same as previous lemma).
  have hMass := dataMass_nonneg a N
  have hStep :
      T.C_ls * (N + Q^2) * (∑ n ∈ Finset.Icc 1 N, ‖a n‖^2)
        ≤ T.C_ls * (N + Q'^2) * (∑ n ∈ Finset.Icc 1 N, ‖a n‖^2) := by
    have hMid : ((N + Q^2 : ℕ) : ℝ) ≤ ((N + Q'^2 : ℕ) : ℝ) :=
      add_sq_mono_in_Q_real hQQ'
    exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hMid hMass)
            (C_ls_nonneg)
  -- But our LHS uses `Icc 1 Q` not `range (Q+1)`. We compare those sums directly.
  -- Define weighted L² mass per modulus and use subset monotonicity.
  let f : ℕ → ℝ := fun q => w q * (∑ r : ZMod q.succ, ‖residueSum a N q r‖^2)
  have f_nonneg : ∀ q, 0 ≤ f q := by
    intro q
    have hw0 := (hw q).left
    have : 0 ≤ (∑ r : ZMod q.succ, ‖residueSum a N q r‖^2) := by
      classical
      refine Finset.sum_nonneg ?h
      intro r _; simpa using (sq_nonneg (‖residueSum a N q r‖ : ℝ))
    exact mul_nonneg hw0 this
  have hSubset : Finset.Icc 1 Q ⊆ Finset.range (Q + 1) := by
    intro q hq
    rcases Finset.mem_Icc.mp hq with ⟨_, hqQ⟩
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le hqQ)
  have h_index :
      (∑ q ∈ Finset.Icc 1 Q, f q)
        ≤ (∑ q ∈ Finset.range (Q + 1), f q) :=
    Finset.sum_le_sum_of_subset_of_nonneg
      hSubset
      (by intro q _ _; exact f_nonneg q)
  -- Chain: `[1,Q]`-sum ≤ `range`-sum ≤ RHS(Q) ≤ RHS(Q').
  have hRangeBound :
      (∑ q ∈ Finset.range (Q + 1), f q)
        ≤ T.C_ls * (N + Q^2) * (∑ n ∈ Finset.Icc 1 N, ‖a n‖^2) := by
    simpa using base
  exact (le_trans h_index (le_trans hRangeBound hStep))

/--
Upgrade the *dyadic* large-sieve RHS from `Q₂` to any `Q₂' ≥ Q₂`.
-/
theorem largeSieve_dyadic_upgrade_Q2
    (T : BVToolbox) (a : ℕ → ℂ) {N Q₁ Q₂ Q₂' : ℕ}
    (hN : 1 ≤ N) (hQ12 : Q₁ ≤ Q₂) (hQ2 : 1 ≤ Q₂) (hQ2le : Q₂ ≤ Q₂') :
    (∑ q ∈ Finset.Icc Q₁ Q₂,
       ∑ r : ZMod q.succ, ‖residueSum a N q r‖^2)
      ≤ T.C_ls * (N + Q₂'^2) * (∑ n ∈ Finset.Icc 1 N, ‖a n‖^2) := by
  -- Base dyadic bound at `Q₂`.
  have h0 := T.largeSieve_residueProgressions_dyadic a hN hQ12 hQ2
  -- Strengthen RHS by bumping `Q₂` to `Q₂'`.
  have hMass := dataMass_nonneg a N
  have hStep :
      T.C_ls * (N + Q₂^2) * (∑ n ∈ Finset.Icc 1 N, ‖a n‖^2)
        ≤ T.C_ls * (N + Q₂'^2) * (∑ n ∈ Finset.Icc 1 N, ‖a n‖^2) := by
    have hMid : ((N + Q₂^2 : ℕ) : ℝ) ≤ ((N + Q₂'^2 : ℕ) : ℝ) :=
      add_sq_mono_in_Q_real hQ2le
    exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hMid hMass)
            (C_ls_nonneg)
  exact le_trans h0 hStep

end Analytic
end Sieve

