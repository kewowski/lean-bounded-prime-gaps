import Mathlib
import Character.Decompositions

/-
Character/Lifting.lean
----------------------
Conservative helpers (ASCII-only):
* `mask` for predicate-masked complex sequences
* `l2NormSq_mask_le` : masking does not increase l² mass
* `l2NormSq_mul_bounded_le` : multiplying by a sequence with ‖b n‖ ≤ 1
   on the summation range does not increase l² mass
-/

open scoped BigOperators
open Finset

namespace Character

/-- Mask a complex sequence by a decidable predicate. -/
def mask (P : ℕ → Prop) [DecidablePred P] (a : ℕ → ℂ) : ℕ → ℂ :=
  fun n => if P n then a n else 0

@[simp] lemma mask_true {P : ℕ → Prop} [DecidablePred P]
    {a : ℕ → ℂ} {n : ℕ} (h : P n) :
    mask P a n = a n := by
  unfold mask; simp [h]

@[simp] lemma mask_false {P : ℕ → Prop} [DecidablePred P]
    {a : ℕ → ℂ} {n : ℕ} (h : ¬ P n) :
    mask P a n = 0 := by
  unfold mask; simp [h]

/-- Masking only decreases the truncated l² mass. -/
lemma l2NormSq_mask_le (N : ℕ) (a : ℕ → ℂ) (P : ℕ → Prop) [DecidablePred P] :
    l2NormSq N (mask P a) ≤ l2NormSq N a := by
  classical
  unfold l2NormSq
  refine sum_le_sum ?term
  intro n hn
  by_cases h : P n
  · simp [mask_true (a := a) h]
  · have : ‖mask P a n‖ = 0 := by simp [mask_false (a := a) h]
    have h0 : (0 : ℝ) ≤ ‖a n‖ ^ 2 := by exact sq_nonneg _
    simp [this]  -- 0 ≤ ‖a n‖^2

/-- If `‖b n‖ ≤ 1` on `range (N+1)`, then multiplying by `b` does not increase the l² mass. -/
lemma l2NormSq_mul_bounded_le
    (N : ℕ) (a b : ℕ → ℂ)
    (hb : ∀ ⦃n⦄, n ∈ Finset.range (N+1) → ‖b n‖ ≤ (1 : ℝ)) :
    l2NormSq N (fun n => a n * b n) ≤ l2NormSq N a := by
  classical
  unfold l2NormSq
  refine sum_le_sum ?term
  intro n hn
  have hb' : ‖b n‖ ≤ (1 : ℝ) := hb hn
  have hA : 0 ≤ ‖a n‖ := norm_nonneg _
  have hB : 0 ≤ ‖b n‖ := norm_nonneg _
  -- Square the inequality ‖b n‖ ≤ 1 by multiplying both sides (nonneg) by themselves
  have hb2 : ‖b n‖ ^ 2 ≤ (1 : ℝ) := by
    have : ‖b n‖ * ‖b n‖ ≤ (1 : ℝ) * 1 :=
      mul_le_mul hb' hb' hB (by norm_num : 0 ≤ (1:ℝ))
    simpa [pow_two] using this
  -- Multiply by the nonnegative factor ‖a n‖^2
  have hsq :
      ‖a n‖ ^ 2 * ‖b n‖ ^ 2 ≤ ‖a n‖ ^ 2 * 1 :=
    mul_le_mul_of_nonneg_left hb2 (by simpa [pow_two] using sq_nonneg (‖a n‖))
  -- Rewrite both sides to the desired norms
  simpa [pow_two, norm_mul, mul_pow, mul_comm, mul_left_comm, mul_assoc] using hsq

end Character
