/-
  Sieve/Analytic/PerModulusCSConvenience.lean
  Per-modulus triangle-inequality bounds (often sufficient in place of CS).

  These give quick upper bounds for a *fixed* residue class `r`:
    • `residue_norm_le_sum_norm`
    • `residueW_norm_le_weighted_sum`
-/
import Mathlib
import Sieve.Analytic.ResidueSumBasics
import Sieve.Analytic.WeightedResidue

noncomputable section
open Classical BigOperators

namespace Sieve
namespace Analytic

/-- For a fixed residue `r`, drop the indicator and bound by the L¹ windowed norm. -/
theorem residue_norm_le_sum_norm
    (a : ℕ → ℂ) (N q : ℕ) (r : ZMod q.succ) :
    ‖residueSum a N q r‖ ≤ ∑ n ∈ Finset.Icc 1 N, ‖a n‖ := by
  classical
  unfold residueSum
  -- Triangle inequality to remove the outer norm.
  have h₁ :
      ‖∑ n ∈ Finset.Icc 1 N,
          (if ((n : ZMod q.succ) = r) then a n else 0)‖
        ≤ ∑ n ∈ Finset.Icc 1 N,
            ‖if ((n : ZMod q.succ) = r) then a n else 0‖ := by
    exact
      (norm_sum_le (s := Finset.Icc 1 N)
                   (f := fun n => (if ((n : ZMod q.succ) = r) then a n else 0)))
  -- Compare each summand with ‖a n‖.
  have h₂ :
      (∑ n ∈ Finset.Icc 1 N,
          ‖if ((n : ZMod q.succ) = r) then a n else 0‖)
        ≤ (∑ n ∈ Finset.Icc 1 N, ‖a n‖) := by
    refine Finset.sum_le_sum ?term
    intro n _hn
    by_cases h : ((n : ZMod q.succ) = r)
    · simp [h]
    ·
      -- Goal reduces to `‖0‖ ≤ ‖a n‖`.
      have hzero :
          ‖if ((n : ZMod q.succ) = r) then a n else 0‖ = 0 := by
        simp [h]
      have hnn : 0 ≤ ‖a n‖ := norm_nonneg _
      rw [hzero]; exact hnn
  exact le_trans h₁ h₂

/-- Weighted version with real weights `w : ℕ → ℝ`. -/
theorem residueW_norm_le_weighted_sum
    (a : ℕ → ℂ) (w : ℕ → ℝ) (N q : ℕ) (r : ZMod q.succ) :
    ‖residueSumW a w N q r‖ ≤ ∑ n ∈ Finset.Icc 1 N, (|w n| * ‖a n‖) := by
  classical
  unfold residueSumW
  -- Triangle inequality to remove the outer norm.
  have h₁ :
      ‖∑ n ∈ Finset.Icc 1 N,
          (if ((n : ZMod q.succ) = r) then ((w n : ℂ) * a n) else 0)‖
        ≤ ∑ n ∈ Finset.Icc 1 N,
            ‖if ((n : ZMod q.succ) = r) then ((w n : ℂ) * a n) else 0‖ := by
    exact
      (norm_sum_le (s := Finset.Icc 1 N)
                   (f := fun n => (if ((n : ZMod q.succ) = r) then ((w n : ℂ) * a n) else 0)))
  -- Compare each summand with |w n|‖a n‖.
  have h₂ :
      (∑ n ∈ Finset.Icc 1 N,
          ‖if ((n : ZMod q.succ) = r) then ((w n : ℂ) * a n) else 0‖)
        ≤ (∑ n ∈ Finset.Icc 1 N, (|w n| * ‖a n‖)) := by
    refine Finset.sum_le_sum ?term
    intro n _hn
    by_cases h : ((n : ZMod q.succ) = r)
    ·
      -- When the indicator is on, rewrite to equality and close with `le_of_eq`.
      have hmul : ‖(w n : ℂ) * a n‖ = |w n| * ‖a n‖ := by
        calc
          ‖(w n : ℂ) * a n‖
              = ‖(w n : ℂ)‖ * ‖a n‖ := by exact (norm_mul ((w n : ℂ)) (a n))
          _   = |w n| * ‖a n‖ := by
                simp [Complex.norm_real]
      -- Rewrite the `if` then apply `hmul` via a short calc chain (no `simpa`).
      have h_if_eq :
          ‖if ((n : ZMod q.succ) = r) then ((w n : ℂ) * a n) else 0‖
            = |w n| * ‖a n‖ := by
        calc
          ‖if ((n : ZMod q.succ) = r) then ((w n : ℂ) * a n) else 0‖
              = ‖(w n : ℂ) * a n‖ := by simp [h]
          _   = |w n| * ‖a n‖ := hmul
      exact le_of_eq h_if_eq
    ·
      -- Otherwise the LHS is `‖0‖`, which is ≤ the RHS by nonnegativity.
      have hzero :
          ‖if ((n : ZMod q.succ) = r) then ((w n : ℂ) * a n) else 0‖ = 0 := by
        simp [h]
      have hn : 0 ≤ |w n| * ‖a n‖ := mul_nonneg (abs_nonneg _) (norm_nonneg _)
      rw [hzero]; exact hn
  exact le_trans h₁ h₂

end Analytic
end Sieve
