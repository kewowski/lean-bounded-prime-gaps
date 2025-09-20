/-
  Sieve/LargeSieve.lean
  Minimal, compiling skeleton: basic `normSq` and `l2NormSq`.
-/

import Mathlib

open scoped BigOperators
open BigOperators

noncomputable section
namespace Sieve

/-- Real square of the complex norm. -/
def normSq (z : ℂ) : ℝ := ‖z‖ ^ 2

/-- Truncated ℓ² mass (sum of squared norms) up to `N`. -/
def l2NormSq (N : ℕ) (a : ℕ → ℂ) : ℝ :=
  ∑ n ∈ Finset.range (N + 1), normSq (a n)

@[simp] lemma normSq_nonneg (z : ℂ) : 0 ≤ normSq z := by
  unfold normSq
  exact sq_nonneg ‖z‖

lemma l2NormSq_nonneg (N : ℕ) (a : ℕ → ℂ) : 0 ≤ l2NormSq N a := by
  classical
  unfold l2NormSq
  refine Finset.sum_nonneg (by
    intro n hn
    exact normSq_nonneg (a n))

end Sieve
end
