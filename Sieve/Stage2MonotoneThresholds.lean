/-
  Sieve/Stage2MonotoneThresholds.lean
  Monotonicity in the threshold τ and basic density bounds.
-/
import Mathlib
import Sieve.MaynardWeights

noncomputable section
open Classical BigOperators

namespace Sieve
namespace Stage2

/-- Heavy set at threshold τ. (Alias used locally for brevity.) -/
private def heavySet (W : Sieve.MaynardWeights.Weight) (τ : ℝ) : Finset ℤ :=
  W.support.filter (fun n => τ ≤ W.w n)

/-- If `τ₁ ≤ τ₂` then the heavy set at `τ₂` is included in the one at `τ₁`. -/
theorem heavySet_subset_of_le
    (W : Sieve.MaynardWeights.Weight) {τ₁ τ₂ : ℝ} (h : τ₁ ≤ τ₂) :
    heavySet W τ₂ ⊆ heavySet W τ₁ := by
  intro n hn
  rcases Finset.mem_filter.mp hn with ⟨hns, hτ2⟩
  refine Finset.mem_filter.mpr ?_
  exact ⟨hns, le_trans h hτ2⟩

/-- Cardinality monotonicity in `τ`: if `τ₁ ≤ τ₂` then
`|heavy(τ₂)| ≤ |heavy(τ₁)|`. (Cast to `ℝ`.) -/
theorem heavy_count_mono_in_tau
    (W : Sieve.MaynardWeights.Weight) {τ₁ τ₂ : ℝ} (h : τ₁ ≤ τ₂) :
    ((heavySet W τ₂).card : ℝ) ≤ ((heavySet W τ₁).card : ℝ) := by
  have hsub := heavySet_subset_of_le (W := W) h
  exact_mod_cast (Finset.card_mono hsub)

/-- Density monotonicity in `τ`: if `τ₁ ≤ τ₂` and `|support|>0`, then
`density(τ₂) ≤ density(τ₁)`. -/
theorem heavy_density_mono_in_tau
    (W : Sieve.MaynardWeights.Weight) {τ₁ τ₂ : ℝ}
    (hpos : 0 < W.support.card) (h : τ₁ ≤ τ₂) :
    ((heavySet W τ₂).card : ℝ) / (W.support.card : ℝ)
      ≤ ((heavySet W τ₁).card : ℝ) / (W.support.card : ℝ) := by
  have hcount := heavy_count_mono_in_tau (W := W) h
  have hden_pos : 0 < (W.support.card : ℝ) := by exact_mod_cast hpos
  exact (div_le_div_of_nonneg_right hcount (le_of_lt hden_pos))

/-- Density is between 0 and 1 (for any `τ`) when support is nonempty. -/
theorem heavy_density_bounds
    (W : Sieve.MaynardWeights.Weight) {τ : ℝ}
    (hpos : 0 < W.support.card) :
    0 ≤ ((heavySet W τ).card : ℝ) / (W.support.card : ℝ)
    ∧ ((heavySet W τ).card : ℝ) / (W.support.card : ℝ) ≤ 1 := by
  -- nonneg: numerator ≥ 0 and denominator > 0
  have hden_pos : 0 < (W.support.card : ℝ) := by exact_mod_cast hpos
  have hden_nonneg : 0 ≤ (W.support.card : ℝ) := le_of_lt hden_pos
  have hden_ne : (W.support.card : ℝ) ≠ 0 := ne_of_gt hden_pos
  have hnum_nonneg : 0 ≤ ((heavySet W τ).card : ℝ) := by
    exact_mod_cast (Nat.zero_le _)
  -- ≤ 1: use subset (heavy ⊆ support) to bound the numerator by |support|
  have hsub : heavySet W τ ⊆ W.support := by
    intro n hn; exact (Finset.mem_filter.mp hn).1
  have hnum_le_den : ((heavySet W τ).card : ℝ) ≤ (W.support.card : ℝ) := by
    exact_mod_cast (Finset.card_mono hsub)
  refine And.intro ?nonneg ?le1
  · exact div_nonneg hnum_nonneg hden_nonneg
  ·
    have := div_le_div_of_nonneg_right hnum_le_den (le_of_lt hden_pos)
    simpa [div_self hden_ne] using this

end Stage2
end Sieve
