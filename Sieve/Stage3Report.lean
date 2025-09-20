/-
  Sieve/Stage3Report.lean
  Stage-3 facing restatements using MTCore (no deep analysis).
-/
import Mathlib
import Sieve.MTCore
import Sieve.Stage2Exports
import Sieve.Stage3Extraction

noncomputable section
open Classical BigOperators

namespace Sieve
namespace Stage3

/-- Density bound from the first moment, framed via `MTCore.heavyDensity`. -/
theorem heavyDensity_le_of_firstMoment_MT
    (W : Sieve.MaynardWeights.Weight) {M τ : ℝ}
    (hpos  : 0 < W.support.card)
    (hτpos : 0 < τ)
    (h_first : (∑ n ∈ W.support, W.w n) ≤ (W.support.card : ℝ) * M) :
    Sieve.MTCore.heavyDensity W τ ≤ M / τ := by
  classical
  -- Unfold `heavyDensity` and apply the Stage-2 bound.
  change
    ((W.support.filter (fun n => τ ≤ W.w n)).card : ℝ) / (W.support.card : ℝ) ≤ M / τ
  simpa using
    Sieve.Stage2.heavy_density_le_of_firstMoment
      (W := W) (M := M) (τ := τ) hpos hτpos h_first

/-- Density bound from the second moment, framed via `MTCore.heavyDensity`. -/
theorem heavyDensity_le_of_secondMoment_MT
    (W : Sieve.MaynardWeights.Weight) {τ : ℝ}
    (hpos : 0 < W.support.card) (hτpos : 0 < τ) :
    Sieve.MTCore.heavyDensity W τ
      ≤ Sieve.MTMoments.secondMoment W / (τ^2 * (W.support.card : ℝ)) := by
  classical
  change
    ((W.support.filter (fun n => τ ≤ W.w n)).card : ℝ) / (W.support.card : ℝ)
      ≤ Sieve.MTMoments.secondMoment W / (τ^2 * (W.support.card : ℝ))
  simpa using
    Sieve.Stage2.heavy_density_le_of_secondMoment (W := W) (τ := τ) hpos hτpos

/-- If `τ ≤ average`, the `τ`-heavy set (non-strict) is nonempty. -/
theorem heavySet_nonempty_of_avg_ge
    (W : Sieve.MaynardWeights.Weight) {τ : ℝ}
    (hpos : 0 < W.support.card)
    (hτleavg : τ ≤ (∑ m ∈ W.support, W.w m) / (W.support.card : ℝ)) :
    (Sieve.MTCore.heavySet W τ).Nonempty := by
  classical
  -- Get a witness from Stage-3 extraction and show it lies in the filtered set.
  obtain ⟨n, hns, hτle⟩ :=
    Sieve.Stage3.exists_heavy_of_avg_ge (W := W) hpos hτleavg
  refine ⟨n, ?_⟩
  exact Finset.mem_filter.mpr ⟨hns, hτle⟩

/-- If `τ ≤ average`, the heavy count is positive (Nat form). -/
theorem heavy_count_pos_of_avg_ge
    (W : Sieve.MaynardWeights.Weight) {τ : ℝ}
    (hpos : 0 < W.support.card)
    (hτleavg : τ ≤ (∑ m ∈ W.support, W.w m) / (W.support.card : ℝ)) :
    0 < (Sieve.MTCore.heavySet W τ).card := by
  classical
  have : (Sieve.MTCore.heavySet W τ).Nonempty :=
    heavySet_nonempty_of_avg_ge (W := W) hpos hτleavg
  exact Finset.card_pos.mpr this

/-- `ℝ`-casted version: if `τ ≤ average`, then `1 ≤ (heavy count : ℝ)`. -/
theorem one_le_heavy_count_real_of_avg_ge
    (W : Sieve.MaynardWeights.Weight) {τ : ℝ}
    (hpos : 0 < W.support.card)
    (hτleavg : τ ≤ (∑ m ∈ W.support, W.w m) / (W.support.card : ℝ)) :
    (1 : ℝ) ≤ ((Sieve.MTCore.heavySet W τ).card : ℝ) := by
  classical
  have hposCard : 0 < (Sieve.MTCore.heavySet W τ).card :=
    heavy_count_pos_of_avg_ge (W := W) hpos hτleavg
  have : 1 ≤ (Sieve.MTCore.heavySet W τ).card := Nat.succ_le_of_lt hposCard
  exact_mod_cast this

end Stage3
end Sieve
