/-
  Sieve/Stage2SecondMomentExtras.lean
  Strict heavy-count variant and empty-set corollaries (strict & non-strict).
-/
import Mathlib
import Sieve.MaynardWeights
import Sieve.MTMoments
import Sieve.Stage2SecondMoment

noncomputable section
open Classical

namespace Sieve
namespace Stage2SecondMoment

/-- Strict Chebyshev-style bound:
`#{n ∈ support(W) | τ < W.w n} ≤ secondMoment(W) / τ^2` for `τ > 0`. -/
theorem heavy_count_strict_le_of_secondMoment
    (W : Sieve.MaynardWeights.Weight) {τ : ℝ} (hτpos : 0 < τ) :
    ((W.support.filter (fun n => τ < W.w n)).card : ℝ)
      ≤ Sieve.MTMoments.secondMoment W / (τ^2) := by
  classical
  set s   : Finset ℤ := W.support
  set Alt : Finset ℤ := s.filter (fun n => τ < W.w n)
  set Ale : Finset ℤ := s.filter (fun n => τ ≤ W.w n)
  -- Strict ⊆ non-strict
  have hsub : Alt ⊆ Ale := by
    intro n hn
    rcases Finset.mem_filter.mp hn with ⟨hns, hlt⟩
    exact Finset.mem_filter.mpr ⟨hns, le_of_lt hlt⟩
  -- Casted card monotonicity
  have hcard : (Alt.card : ℝ) ≤ (Ale.card : ℝ) := by
    exact_mod_cast (Finset.card_mono hsub)
  -- Apply the main (non-strict) bound and combine
  have hmain :
      (Ale.card : ℝ) ≤ Sieve.MTMoments.secondMoment W / (τ^2) := by
    simpa [s, Ale] using (heavy_count_le_of_secondMoment (W := W) hτpos)
  exact le_trans hcard hmain

/-- If `secondMoment(W) < τ^2` with `τ > 0`, then the **strict** heavy set is empty. -/
theorem heavy_strict_empty_of_secondMoment_lt
    (W : Sieve.MaynardWeights.Weight) {τ : ℝ}
    (hτpos : 0 < τ)
    (hsm : Sieve.MTMoments.secondMoment W < τ^2) :
    (W.support.filter (fun n => τ < W.w n)).card = 0 := by
  classical
  set s   : Finset ℤ := W.support
  set Alt : Finset ℤ := s.filter (fun n => τ < W.w n)
  have hτ2pos : 0 < τ^2 := by simpa [pow_two] using mul_pos hτpos hτpos
  have hτ2ne  : τ^2 ≠ 0 := ne_of_gt hτ2pos
  -- From `secondMoment < τ^2` deduce `secondMoment / τ^2 < 1`.
  have hlt1 : Sieve.MTMoments.secondMoment W / (τ^2) < 1 := by
    have := div_lt_div_of_pos_right hsm hτ2pos
    simpa [div_self hτ2ne] using this
  -- Bound the strict heavy count, then force card = 0.
  have hbound := heavy_count_strict_le_of_secondMoment (W := W) hτpos
  have hlt : (Alt.card : ℝ) < 1 := lt_of_le_of_lt (by simpa [s, Alt] using hbound) hlt1
  by_contra hne
  have h1le : (1 : ℝ) ≤ (Alt.card : ℝ) := by
    have : 1 ≤ Alt.card := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hne)
    exact_mod_cast this
  exact (not_le_of_gt hlt) h1le

/-- If `secondMoment(W) < τ^2` with `τ > 0`, then the **non-strict** heavy set is empty. -/
theorem heavy_nonstrict_empty_of_secondMoment_lt
    (W : Sieve.MaynardWeights.Weight) {τ : ℝ}
    (hτpos : 0 < τ)
    (hsm : Sieve.MTMoments.secondMoment W < τ^2) :
    (W.support.filter (fun n => τ ≤ W.w n)).card = 0 := by
  classical
  set s   : Finset ℤ := W.support
  set Ale : Finset ℤ := s.filter (fun n => τ ≤ W.w n)
  have hτ2pos : 0 < τ^2 := by simpa [pow_two] using mul_pos hτpos hτpos
  have hτ2ne  : τ^2 ≠ 0 := ne_of_gt hτ2pos
  have hlt1 : Sieve.MTMoments.secondMoment W / (τ^2) < 1 := by
    have := div_lt_div_of_pos_right hsm hτ2pos
    simpa [div_self hτ2ne] using this
  have hbound := heavy_count_le_of_secondMoment (W := W) hτpos
  have hlt : (Ale.card : ℝ) < 1 := lt_of_le_of_lt (by simpa [s, Ale] using hbound) hlt1
  by_contra hne
  have h1le : (1 : ℝ) ≤ (Ale.card : ℝ) := by
    have : 1 ≤ Ale.card := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hne)
    exact_mod_cast this
  exact (not_le_of_gt hlt) h1le

end Stage2SecondMoment
end Sieve
