/-
  Sieve/Analytic/IndexCounting.lean
  Small, stable conveniences for working with the window `Finset.Icc 1 N`.

  Contents:
    • `Icc_one_subset_range_succ` :  `[1..N] ⊆ range (N+1)`
    • `sum_one_Icc_card`          :  `∑_{n=1}^N 1 = card [1..N]`
    • `sum_Icc_nonneg_of_nonneg`  :  nonnegativity of sums over `[1..N]`
-/
import Mathlib

noncomputable section
open Classical BigOperators

namespace Sieve
namespace Analytic

/-- Membership-wise: every `1 ≤ n ≤ N` satisfies `n < N+1`. -/
lemma Icc_one_subset_range_succ (N : ℕ) :
    (Finset.Icc 1 N) ⊆ (Finset.range (N+1)) := by
  intro n hn
  -- Use `n` explicitly so the linter doesn't complain it is unused.
  have hn_le : n ≤ N := (Finset.mem_Icc.mp hn).2
  exact Finset.mem_range.mpr (Nat.lt_succ_of_le hn_le)

/-- Over reals: the sum of ones on `[1..N]` equals the cardinality. -/
lemma sum_one_Icc_card (N : ℕ) :
    (∑ _ ∈ Finset.Icc 1 N, (1 : ℝ)) = (Finset.card (Finset.Icc 1 N) : ℝ) := by
  classical
  simp [Finset.sum_const, nsmul_eq_mul]

/-- If `b n ≥ 0` on `[1..N]`, then the sum over `[1..N]` is nonnegative. -/
lemma sum_Icc_nonneg_of_nonneg {N : ℕ} (b : ℕ → ℝ)
    (h : ∀ n ∈ Finset.Icc 1 N, 0 ≤ b n) :
    0 ≤ (∑ n ∈ Finset.Icc 1 N, b n) := by
  classical
  exact Finset.sum_nonneg (by intro n hn; exact h n hn)

end Analytic
end Sieve
