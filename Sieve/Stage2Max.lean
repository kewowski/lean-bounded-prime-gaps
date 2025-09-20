/-
  Sieve/Stage2Max.lean
  Existence of a maximizer with value ≥ the average on the support (robust version).
-/
import Mathlib
import Sieve.MaynardWeights

noncomputable section
open Classical
open scoped BigOperators

namespace Sieve.Stage2

/-- On any nonempty finite set, there exists a maximizer `n` of `f` on `s`
    such that `f n` is at least the average of `f` over `s`. -/
lemma exists_max_ge_avg_on_support
    (s : Finset ℤ) (f : ℤ → ℝ) (hpos : 0 < s.card) :
    ∃ n ∈ s, (∀ m ∈ s, f m ≤ f n) ∧ (∑ x ∈ s, f x) / (s.card : ℝ) ≤ f n := by
  classical
  -- pick a maximizer of f on s
  obtain ⟨n, hn, hmax⟩ := s.exists_max_image f (Finset.card_pos.mp hpos)
  -- sum ≤ card * max
  have sum_le : ∑ x ∈ s, f x ≤ (s.card : ℝ) * f n := by
    have : ∑ x ∈ s, f x ≤ ∑ _x ∈ s, f n :=
      Finset.sum_le_sum (fun x hx => hmax x hx)
    simpa [Finset.sum_const, nsmul_eq_mul, mul_comm] using this
  -- divide by card > 0
  have hcpos : 0 < (s.card : ℝ) := by exact_mod_cast hpos
  have hcz : (s.card : ℝ) ≠ 0 := ne_of_gt hcpos
  have avg_le_max : (∑ x ∈ s, f x) / (s.card : ℝ) ≤ f n := by
    have := mul_le_mul_of_nonneg_right sum_le (le_of_lt (inv_pos.mpr hcpos))
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc, hcz] using this
  exact ⟨n, hn, hmax, avg_le_max⟩

/-- Specialization to `Weight`: there exists `n` in the support maximizing `W.w`
    with `W.w n ≥` the average weight. -/
lemma exists_maxWeight_ge_average
    (W : Sieve.MaynardWeights.Weight)
    (hpos : 0 < W.support.card) :
    ∃ n ∈ W.support,
      (∀ m ∈ W.support, W.w m ≤ W.w n) ∧
      (∑ x ∈ W.support, W.w x) / (W.support.card : ℝ) ≤ W.w n := by
  simpa using
    exists_max_ge_avg_on_support W.support W.w hpos

end Sieve.Stage2
