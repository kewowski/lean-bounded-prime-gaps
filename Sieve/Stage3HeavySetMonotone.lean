/-
  Sieve/Stage3HeavySetMonotone.lean
  Heavy set shrinks as the threshold τ increases; cardinality is nonincreasing.
-/
import Mathlib
import Sieve.MTCore

noncomputable section
open Classical BigOperators

namespace Sieve
namespace Stage3

/-- If `τ₁ ≤ τ₂`, then `heavySet W τ₂ ⊆ heavySet W τ₁`. -/
theorem heavySet_subset_of_tau_le
    (W : Sieve.MaynardWeights.Weight) {τ₁ τ₂ : ℝ}
    (hτ : τ₁ ≤ τ₂) :
    Sieve.MTCore.heavySet W τ₂ ⊆ Sieve.MTCore.heavySet W τ₁ := by
  classical
  intro n hn2
  rcases Finset.mem_filter.1 hn2 with ⟨hns, hτ2⟩
  exact Finset.mem_filter.2 ⟨hns, le_trans hτ hτ2⟩

/-- Monotonicity of heavy-set cardinality in τ (nonincreasing). -/
theorem heavy_card_mono_in_tau
    (W : Sieve.MaynardWeights.Weight) {τ₁ τ₂ : ℝ}
    (hτ : τ₁ ≤ τ₂) :
    (Sieve.MTCore.heavySet W τ₂).card ≤ (Sieve.MTCore.heavySet W τ₁).card := by
  classical
  -- Work on `s = support`, view heavy sets as filters on `s`.
  set s  : Finset ℤ := W.support
  set P1 : ℤ → Prop := fun n => τ₁ ≤ W.w n
  set P2 : ℤ → Prop := fun n => τ₂ ≤ W.w n
  set A1 : Finset ℤ := s.filter P1
  set A2 : Finset ℤ := s.filter P2
  -- Pointwise: 1_{P2} ≤ 1_{P1} on s.
  have hpt :
      ∀ n ∈ s, (if P2 n then (1 : ℝ) else 0) ≤ (if P1 n then 1 else 0) := by
    intro n hn
    by_cases hp2 : P2 n
    · have hp1 : P1 n := le_trans hτ hp2; simp [hp2, hp1]
    · by_cases hp1 : P1 n
      · simp [hp2, hp1]   -- 0 ≤ 1
      · simp [hp2, hp1]   -- 0 ≤ 0
  -- Sum inequality on s.
  have hsum_le :
      (∑ n ∈ s, (if P2 n then (1 : ℝ) else 0))
        ≤ (∑ n ∈ s, (if P1 n then 1 else 0)) :=
    Finset.sum_le_sum (by intro n hn; exact hpt n hn)
  -- Turn both sums into cardinals.
  have hleft :=
    (Finset.sum_filter (s := s) (p := P2) (f := fun _ => (1 : ℝ))).symm
  have hright :=
    (Finset.sum_filter (s := s) (p := P1) (f := fun _ => (1 : ℝ))).symm
  -- Normalize both sides
  simp [Finset.sum_const, nsmul_eq_mul] at hleft
  simp [Finset.sum_const, nsmul_eq_mul] at hright
  -- Cast down to `ℕ` inequality.
  have hcard_real : (A2.card : ℝ) ≤ (A1.card : ℝ) := by
    simpa [hleft, hright] using hsum_le
  have hcard_nat : A2.card ≤ A1.card := by
    exact_mod_cast hcard_real
  -- Rewrite heavy sets back from `A1/A2`.
  simpa [Sieve.MTCore.heavySet, s, A1, A2, P1, P2]

end Stage3
end Sieve
