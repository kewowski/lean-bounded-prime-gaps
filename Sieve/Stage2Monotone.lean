/-
  Sieve/Stage2Monotone.lean
  (1) Monotonicity in the threshold for heavy counts.
  (2) At least one heavy point at the average (nonempty support).
-/
import Mathlib
import Sieve.MaynardWeights
import Sieve.Stage2Pigeonhole  -- for exists_heavy_ge_average

noncomputable section
open Classical
open scoped BigOperators

namespace Sieve.Stage2

/-- Monotonicity: if `τ₁ ≤ τ₂` then
    `#{n | W.w n ≥ τ₂} ≤ #{n | W.w n ≥ τ₁}`. -/
lemma heavy_count_mono
    (W : Sieve.MaynardWeights.Weight)
    {τ₁ τ₂ : ℝ} (h : τ₁ ≤ τ₂) :
    (W.support.filter (fun n => τ₂ ≤ W.w n)).card
      ≤ (W.support.filter (fun n => τ₁ ≤ W.w n)).card := by
  classical
  set s  : Finset ℤ := W.support
  set A1 : Finset ℤ := s.filter (fun n => τ₁ ≤ W.w n)
  set A2 : Finset ℤ := s.filter (fun n => τ₂ ≤ W.w n)
  -- Key: A2 = A1 filtered again by (τ₂ ≤ W.w n), since τ₂ ≤ W.w ⇒ τ₁ ≤ W.w.
  have A2_eq : A2 = A1.filter (fun n => τ₂ ≤ W.w n) := by
    ext n; constructor
    · intro hn
      rcases Finset.mem_filter.mp hn with ⟨hn_s, h2⟩
      have h1 : τ₁ ≤ W.w n := le_trans h h2
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hn_s, h1⟩, h2⟩
    · intro hn
      rcases Finset.mem_filter.mp hn with ⟨hnA1, h2⟩
      rcases Finset.mem_filter.mp hnA1 with ⟨hn_s, _h1⟩
      exact Finset.mem_filter.mpr ⟨hn_s, h2⟩
  -- Now use `card_filter_le` on `A1`.
  have : A2.card ≤ A1.card := by
    simpa [A2_eq] using (Finset.card_filter_le (s := A1) (p := fun n => τ₂ ≤ W.w n))
  simpa [s, A1, A2] using this

/-- If the support is nonempty, then at the **average weight**
    there is at least one heavy point. -/
lemma heavy_count_at_avg_pos
    (W : Sieve.MaynardWeights.Weight)
    (hpos : 0 < W.support.card) :
    0 < (W.support.filter
          (fun n => ((∑ x ∈ W.support, W.w x) / (W.support.card : ℝ)) ≤ W.w n)
        ).card := by
  classical
  obtain ⟨n, hn, h⟩ := exists_heavy_ge_average W hpos
  refine Finset.card_pos.mpr ?_
  refine ⟨n, ?_⟩
  -- n belongs to the heavy set at the average
  simpa [Finset.mem_filter] using And.intro hn h

end Sieve.Stage2
