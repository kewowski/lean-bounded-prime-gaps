/-
  Sieve/Stage2Thresholds.lean
  First-moment (Markov-style) heavy-count bound:
  If `∑_{support} w ≤ |support| * M` and `τ > 0`, then
  `#{n ∈ support | τ ≤ w n} ≤ |support| * M / τ`.

  Works directly on A := support.filter (τ ≤ w n).
-/
import Mathlib
import Sieve.MaynardWeights
import Sieve.MTMoments

noncomputable section
open Classical BigOperators

namespace Sieve
namespace Stage2

/-- Markov 1st-moment threshold bound (division form). -/
theorem heavy_count_le_of_firstMoment
    (W : Sieve.MaynardWeights.Weight) {M τ : ℝ}
    (hτpos : 0 < τ)
    (h_first : (∑ n ∈ W.support, W.w n)
               ≤ (W.support.card : ℝ) * M) :
    ((W.support.filter (fun n => τ ≤ W.w n)).card : ℝ)
      ≤ (W.support.card : ℝ) * M / τ := by
  classical
  set s : Finset ℤ := W.support
  set A : Finset ℤ := s.filter (fun n => τ ≤ W.w n)

  have hτne : τ ≠ 0 := ne_of_gt hτpos

  -- On A we have τ ≤ w n
  have hpt : ∀ n ∈ A, τ ≤ W.w n := by
    intro n hn; exact (Finset.mem_filter.mp hn).2

  -- Sum over A: (A.card)*τ ≤ ∑_{A} w
  have hA_le_sumA : (A.card : ℝ) * τ ≤ ∑ n ∈ A, W.w n := by
    have := Finset.sum_le_sum (by intro n hn; exact hpt n hn)
    simpa [Finset.sum_const, nsmul_eq_mul] using this

  -- Monotonicity A ⊆ s: ∑_{A} w ≤ ∑_{s} w
  have hsub : A ⊆ s := by intro n hn; exact (Finset.mem_filter.mp hn).1
  have hsum_mono : ∑ n ∈ A, W.w n ≤ ∑ n ∈ s, W.w n := by
    refine Finset.sum_le_sum_of_subset_of_nonneg hsub ?_
    intro n hns _; exact W.nonneg n

  -- Chain: (A.card)*τ ≤ |s|*M
  have hchain : (A.card : ℝ) * τ ≤ (s.card : ℝ) * M :=
    le_trans (le_trans hA_le_sumA hsum_mono) (by simpa [s] using h_first)

  -- Divide both sides by τ (order-preserving since τ > 0).
  have hdiv :
      ((A.card : ℝ) * τ) / τ
        ≤ ((s.card : ℝ) * M) / τ :=
    div_le_div_of_nonneg_right hchain (le_of_lt hτpos)

  -- Simplify the left
  have : (A.card : ℝ) ≤ (s.card : ℝ) * M / τ := by
    simpa [mul_div_assoc, div_self hτne, one_mul] using hdiv

  -- Rewrite names
  simpa [s, A] using this

end Stage2
end Sieve
