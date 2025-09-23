/-
  Sieve/Analytic/L1WeightedIccConvenience.lean
  Small conveniences for L¹-type expressions over the window `Finset.Icc 1 N`.
-/
import Mathlib

noncomputable section
open Classical BigOperators

namespace Sieve
namespace Analytic

/-- Pull a constant absolute value outside an L¹-type sum over `Icc 1 N`. -/
lemma sum_abs_const_mul_norm
    (c : ℝ) (a : ℕ → ℂ) (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, (|c| * ‖a n‖))
      = |c| * (∑ n ∈ Finset.Icc 1 N, ‖a n‖) := by
  classical
  simpa using
    (Finset.mul_sum (a := |c|)
      (s := Finset.Icc 1 N)
      (f := fun n => ‖a n‖)).symm

/-- The basic nonnegativity of an L¹-type sum with absolute weights. -/
lemma sum_absw_norm_nonneg
    (w : ℕ → ℝ) (a : ℕ → ℂ) (N : ℕ) :
    0 ≤ (∑ n ∈ Finset.Icc 1 N, (|w n| * ‖a n‖)) := by
  classical
  refine Finset.sum_nonneg ?_
  intro n hn
  exact mul_nonneg (abs_nonneg _) (norm_nonneg _)

end Analytic
end Sieve
