/-
  Sieve/Stage3Extraction.lean
  Minimal Stage-3 glue: extract a heavy point from an average bound.
-/
import Mathlib
import Sieve.MaynardWeights

noncomputable section
open Classical BigOperators

namespace Sieve
namespace Stage3

/-- There exists a point with value at least the average (nonempty support). -/
theorem exists_heavy_at_average
    (W : Sieve.MaynardWeights.Weight)
    (hpos : 0 < W.support.card) :
    ∃ n ∈ W.support,
      (∑ m ∈ W.support, W.w m) / (W.support.card : ℝ) ≤ W.w n := by
  classical
  set s : Finset ℤ := W.support
  have hsne : s.Nonempty := Finset.card_pos.mp (by simpa [s] using hpos)
  -- pick n maximizing W.w on s
  obtain ⟨n, hn, hmax⟩ := Finset.exists_max_image s (fun m => W.w m) hsne
  -- sum ≤ card * max
  have hsum_le :
      (∑ m ∈ s, W.w m) ≤ (s.card : ℝ) * W.w n := by
    have : ∑ m ∈ s, W.w m ≤ ∑ _m ∈ s, W.w n :=
      Finset.sum_le_sum (by intro m hm; exact hmax m hm)
    simpa [Finset.sum_const, nsmul_eq_mul, mul_comm] using this
  -- divide by |s| > 0
  have hscard_pos : 0 < (s.card : ℝ) := by exact_mod_cast (by simpa [s] using hpos)
  have hscard_ne : (s.card : ℝ) ≠ 0 := ne_of_gt hscard_pos
  have hdiv :
      (∑ m ∈ s, W.w m) / (s.card : ℝ)
        ≤ ((s.card : ℝ) * W.w n) / (s.card : ℝ) :=
    div_le_div_of_nonneg_right hsum_le (le_of_lt hscard_pos)
  -- simplify RHS to w n
  have rhs_eq : ((s.card : ℝ) * W.w n) / (s.card : ℝ) = W.w n := by
    calc
      ((s.card : ℝ) * W.w n) / (s.card : ℝ)
          = (W.w n * (s.card : ℝ)) / (s.card : ℝ) := by
              simp [mul_comm]
      _   = W.w n * ((s.card : ℝ) / (s.card : ℝ)) := by
              simp [mul_div_assoc]
      _   = W.w n := by
              simp [div_self hscard_ne]
  have : (∑ m ∈ s, W.w m) / (s.card : ℝ) ≤ W.w n := by
    simpa [rhs_eq] using hdiv
  exact ⟨n, by simpa [s] using hn, this⟩

/-- If `τ ≤ average`, then some point is `τ`-heavy (nonempty support). -/
theorem exists_heavy_of_avg_ge
    (W : Sieve.MaynardWeights.Weight) {τ : ℝ}
    (hpos : 0 < W.support.card)
    (hτleavg : τ ≤ (∑ m ∈ W.support, W.w m) / (W.support.card : ℝ)) :
    ∃ n ∈ W.support, τ ≤ W.w n := by
  classical
  obtain ⟨n, hn, havg_le⟩ := exists_heavy_at_average (W := W) hpos
  exact ⟨n, hn, le_trans hτleavg havg_le⟩

end Stage3
end Sieve


