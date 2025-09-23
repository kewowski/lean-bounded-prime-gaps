/-
  Sieve/Analytic/L1Monotonicity.lean
  Monotonicity in `N` for L¹-type windowed sums over `Finset.Icc 1 N`.
-/
import Mathlib

noncomputable section
open Classical BigOperators

namespace Sieve
namespace Analytic

/-- `Icc 1 N ⊆ Icc 1 M` when `N ≤ M`. -/
lemma Icc_one_subset_Icc_of_le {N M : ℕ} (hNM : N ≤ M) :
    (Finset.Icc 1 N) ⊆ (Finset.Icc 1 M) := by
  intro n hn
  rcases Finset.mem_Icc.mp hn with ⟨h1, hN⟩
  exact Finset.mem_Icc.mpr ⟨h1, le_trans hN hNM⟩

/-- L¹ monotonicity (unweighted): the windowed sum of norms is monotone in `N`. -/
lemma sum_norm_Icc_monotone_in_N
    (a : ℕ → ℂ) {N M : ℕ} (hNM : N ≤ M) :
    (∑ n ∈ Finset.Icc 1 N, ‖a n‖)
      ≤ (∑ n ∈ Finset.Icc 1 M, ‖a n‖) := by
  classical
  refine
    Finset.sum_le_sum_of_subset_of_nonneg (Icc_one_subset_Icc_of_le hNM) ?hn
  intro n hnT hn_notS
  exact norm_nonneg (a n)

/-- L¹ monotonicity with absolute real weights `|w n|`. -/
lemma sum_absw_norm_Icc_monotone_in_N
    (w : ℕ → ℝ) (a : ℕ → ℂ) {N M : ℕ} (hNM : N ≤ M) :
    (∑ n ∈ Finset.Icc 1 N, (|w n| * ‖a n‖))
      ≤ (∑ n ∈ Finset.Icc 1 M, (|w n| * ‖a n‖)) := by
  classical
  refine
    Finset.sum_le_sum_of_subset_of_nonneg (Icc_one_subset_Icc_of_le hNM) ?hn
  intro n hnT hn_notS
  exact mul_nonneg (abs_nonneg _) (norm_nonneg (a n))

end Analytic
end Sieve
