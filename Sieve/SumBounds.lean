/-
  Sieve/SumBounds.lean
  Generic finite-sum inequality: if f x ≤ M on a finite set s, then
  ∑ x ∈ s, f x ≤ (s.card : ℝ) * M.
-/
import Mathlib

noncomputable section
open Classical

namespace Sieve.SumBounds

/-- If `f x ≤ M` on a finite set `s`, then `∑ x ∈ s, f x ≤ (s.card : ℝ) * M`. -/
lemma sum_le_card_mul_bound {α : Type*} [DecidableEq α]
    (s : Finset α) (f : α → ℝ) (M : ℝ)
    (hub : ∀ x ∈ s, f x ≤ M) :
    (∑ x ∈ s, f x) ≤ (s.card : ℝ) * M := by
  have : (∑ x ∈ s, f x) ≤ (∑ x ∈ s, M) := by
    refine Finset.sum_le_sum ?_ ; intro x hx ; exact hub x hx
  -- `∑ x ∈ s, M = (s.card : ℝ) * M`
  simpa [Finset.sum_const, nsmul_eq_mul] using this

end Sieve.SumBounds
