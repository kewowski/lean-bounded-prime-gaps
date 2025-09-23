/-
  Sieve/Analytic/ResidueSumBasics.lean
  Core definitions and a basic triangle-inequality bound used everywhere.
-/
import Mathlib

noncomputable section
open Classical BigOperators

namespace Sieve
namespace Analytic

/-- Sum over `n ∈ [1, N]` of `a n` restricted to the residue class `r (mod q+1)`. -/
def residueSum (a : ℕ → ℂ) (N q : ℕ) (r : ZMod q.succ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N, if ((n : ZMod q.succ) = r) then a n else 0

/-- L² mass across residues for modulus `q`. -/
def residueMass (a : ℕ → ℂ) (N q : ℕ) : ℝ :=
  ∑ r : ZMod q.succ, ‖residueSum a N q r‖^2

@[simp] lemma residueMass_def (a : ℕ → ℂ) (N q : ℕ) :
    residueMass a N q = ∑ r : ZMod q.succ, ‖residueSum a N q r‖^2 := rfl

/--
Triangle-inequality bound (drop the indicator, then sum of norms bounds the norm of the sum).
-/
theorem norm_residueSum_le_sum_norm (a : ℕ → ℂ) (N q : ℕ) (r : ZMod q.succ) :
    ‖residueSum a N q r‖ ≤ ∑ n ∈ Finset.Icc 1 N, ‖a n‖ := by
  classical
  -- First bound by the sum of the norms of the summands.
  have h₁ :
      ‖residueSum a N q r‖
        ≤ ∑ n ∈ Finset.Icc 1 N,
            ‖if ((n : ZMod q.succ) = r) then a n else 0‖ := by
    unfold residueSum
    exact
      (norm_sum_le (s := Finset.Icc 1 N)
                   (f := fun n => (if ((n : ZMod q.succ) = r) then a n else 0)))
  -- Then compare each summand with ‖a n‖.
  have h₂ :
      (∑ n ∈ Finset.Icc 1 N,
          ‖if ((n : ZMod q.succ) = r) then a n else 0‖)
        ≤ (∑ n ∈ Finset.Icc 1 N, ‖a n‖) := by
    refine Finset.sum_le_sum ?term
    intro n _hn
    by_cases h : ((n : ZMod q.succ) = r)
    · -- Indicator true: both sides are ‖a n‖.
      simp [h]
    · -- Indicator false: LHS is ‖0‖ = 0, so `0 ≤ ‖a n‖`.
      have hLHS : ‖if ((n : ZMod q.succ) = r) then a n else 0‖ = 0 := by
        simp [h]
      rw [hLHS]
      exact norm_nonneg _
  exact le_trans h₁ h₂

/-- Nonnegativity of the L² mass across residues. -/
theorem residueMass_nonneg (a : ℕ → ℂ) (N q : ℕ) :
    0 ≤ residueMass a N q := by
  classical
  unfold residueMass
  refine Finset.sum_nonneg ?h
  intro r _
  exact sq_nonneg (‖residueSum a N q r‖ : ℝ)

end Analytic
end Sieve
