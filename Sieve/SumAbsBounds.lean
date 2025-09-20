/-
  Sieve/SumAbsBounds.lean
  Triangle-inequality sum bounds and their squared corollary.
-/
import Mathlib
import Sieve.SumBounds

noncomputable section
open Classical
open scoped BigOperators

namespace Sieve.SumAbsBounds

/-- If `|f x| ≤ M` on a finite set `s`, then `|∑ x ∈ s, f x| ≤ (s.card : ℝ) * M`. -/
lemma abs_sum_le_card_mul_bound {α : Type*} [DecidableEq α]
    (s : Finset α) (f : α → ℝ) (M : ℝ)
    (habs : ∀ x ∈ s, |f x| ≤ M) :
    |∑ x ∈ s, f x| ≤ (s.card : ℝ) * M := by
  -- Triangle inequality: `|∑ f| ≤ ∑ |f|`.
  have tri : |∑ x ∈ s, f x| ≤ (∑ x ∈ s, |f x|) := by
    simpa using Finset.abs_sum_le_sum_abs (s := s) (f := fun x => f x)
  -- Bound `∑ |f|` by `(#s)·M`.
  have up : (∑ x ∈ s, |f x|) ≤ (s.card : ℝ) * M := by
    simpa using
      Sieve.SumBounds.sum_le_card_mul_bound (s := s) (f := fun x => |f x|) (M := M)
        (hub := habs)
  exact le_trans tri up

/-- Squared corollary: if `0 ≤ M` and `|f x| ≤ M` on `s`, then
    `(∑ x ∈ s, f x)^2 ≤ (s.card : ℝ)^2 * M^2`. -/
lemma sum_sq_le_card_sq_mul_bound_sq {α : Type*} [DecidableEq α]
    (s : Finset α) (f : α → ℝ) (M : ℝ)
    (hM : 0 ≤ M)
    (habs : ∀ x ∈ s, |f x| ≤ M) :
    (∑ x ∈ s, f x)^2 ≤ (s.card : ℝ)^2 * M^2 := by
  -- From the previous lemma: `|Σ f| ≤ (#s)·M`.
  have h₁ : |∑ x ∈ s, f x| ≤ (s.card : ℝ) * M :=
    abs_sum_le_card_mul_bound s f M habs
  -- Upgrade RHS to an absolute value to apply `sq_le_sq` directly.
  have h₂ : |∑ x ∈ s, f x| ≤ |(s.card : ℝ) * M| := by
    -- Since `M ≥ 0` and `(s.card : ℝ) ≥ 0`, `|(s.card)*M| = (s.card)*M`.
    have hcard : 0 ≤ (s.card : ℝ) := by
      simpa using (Nat.cast_nonneg s.card)
    simpa [abs_of_nonneg (mul_nonneg hcard hM)] using h₁
  -- Square both sides: `a^2 ≤ b^2` from `|a| ≤ |b|`.
  have hsq : (∑ x ∈ s, f x)^2 ≤ ((s.card : ℝ) * M)^2 :=
    (sq_le_sq.mpr h₂)
  -- Expand `(a*b)^2 = a^2 * b^2` and tidy.
  simpa [mul_pow, pow_two, mul_comm, mul_left_comm, mul_assoc] using hsq

end Sieve.SumAbsBounds
