/-
  Sieve/Stage3DensityMonotone.lean
  Heavy density is antitone in τ: if τ₁ ≤ τ₂ then heavyDensity W τ₂ ≤ heavyDensity W τ₁.
-/
import Mathlib
import Sieve.MTCore

noncomputable section
open Classical BigOperators

namespace Sieve
namespace Stage3

/-- If `τ₁ ≤ τ₂`, the heavy set shrinks, so the heavy **density** is antitone in `τ`. -/
theorem heavyDensity_antitone_in_tau
    (W : Sieve.MaynardWeights.Weight) {τ₁ τ₂ : ℝ} (hτ : τ₁ ≤ τ₂) :
    Sieve.MTCore.heavyDensity W τ₂ ≤ Sieve.MTCore.heavyDensity W τ₁ := by
  classical
  set s  : Finset ℤ := W.support
  set P1 : ℤ → Prop := fun n => τ₁ ≤ W.w n
  set P2 : ℤ → Prop := fun n => τ₂ ≤ W.w n
  set A1 : Finset ℤ := s.filter P1
  set A2 : Finset ℤ := s.filter P2
  -- Pointwise on s: 1_{P2} ≤ 1_{P1}
  have hpt : ∀ n ∈ s, (if P2 n then (1 : ℝ) else 0) ≤ (if P1 n then 1 else 0) := by
    intro n hn; by_cases h2 : P2 n
    · have h1n : P1 n := le_trans hτ h2
      simp [h2, h1n]
    · have : 0 ≤ (if P1 n then (1 : ℝ) else 0) := by
        by_cases h1 : P1 n <;> simp [h1]
      simpa [h2] using this
  -- Sum to get (A2.card : ℝ) ≤ (A1.card : ℝ)
  have hsum :
      (∑ n ∈ s, (if P2 n then (1 : ℝ) else 0))
        ≤ (∑ n ∈ s, (if P1 n then (1 : ℝ) else 0)) :=
    Finset.sum_le_sum (by intro n hn; exact hpt n hn)
  have hcard : (A2.card : ℝ) ≤ (A1.card : ℝ) := by
    have hswap2 := (Finset.sum_filter (s := s) (p := P2) (f := fun _ => (1 : ℝ))).symm
    have hswap1 := (Finset.sum_filter (s := s) (p := P1) (f := fun _ => (1 : ℝ))).symm
    simp [Finset.sum_const, nsmul_eq_mul] at hswap2 hswap1
    simpa [hswap2, hswap1] using hsum
  -- Divide by |s| (nonnegative, inv 0 = 0 in ℝ so this is safe without s ≠ ∅)
  have hden : 0 ≤ (s.card : ℝ) := by exact_mod_cast (Nat.zero_le _)
  have := div_le_div_of_nonneg_right hcard hden
  simpa [Sieve.MTCore.heavyDensity, s, A1, A2] using this

end Stage3
end Sieve

