/-
  Sieve/Stage3Monotone.lean
  Heavy-density is antitone in the threshold τ (Stage-3 / MTCore view).
-/
import Mathlib
import Sieve.MTCore


noncomputable section
open Classical BigOperators

namespace Sieve
namespace Stage3

/-- For `τ₁ ≤ τ₂` and `0 < |support|`, the heavy density is antitone:
`heavyDensity τ₂ ≤ heavyDensity τ₁`. -/
theorem heavyDensity_antitone_in_tau
    (W : Sieve.MaynardWeights.Weight) {τ₁ τ₂ : ℝ}
    (hτ : τ₁ ≤ τ₂) (hpos : 0 < W.support.card) :
    Sieve.MTCore.heavyDensity W τ₂ ≤ Sieve.MTCore.heavyDensity W τ₁ := by
  classical
  set s  : Finset ℤ := W.support
  set P1 : ℤ → Prop := fun n => τ₁ ≤ W.w n
  set P2 : ℤ → Prop := fun n => τ₂ ≤ W.w n
  set A1 : Finset ℤ := s.filter P1
  set A2 : Finset ℤ := s.filter P2
  -- Pointwise indicator inequality on s: 1_{P2} ≤ 1_{P1}
  have hpt :
      ∀ n ∈ s, (if P2 n then (1 : ℝ) else 0) ≤ (if P1 n then 1 else 0) := by
    intro n hn
    by_cases hp2 : P2 n
    · have hp1 : P1 n := le_trans hτ hp2
      simp [hp2, hp1]
    · by_cases hp1 : P1 n
      · simp [hp2, hp1]   -- 0 ≤ 1
      · simp [hp2, hp1]   -- 0 ≤ 0
  -- Sum over s of indicators gives card of filtered sets
  have hsum_le :
      (∑ n ∈ s, (if P2 n then (1 : ℝ) else 0))
        ≤ (∑ n ∈ s, (if P1 n then 1 else 0)) :=
    Finset.sum_le_sum (by intro n hn; exact hpt n hn)
  have hleft :
      (∑ n ∈ s, (if P2 n then (1 : ℝ) else 0)) = (A2.card : ℝ) := by
    -- ∑_s ite → ∑_{s.filter P2} 1 → card
    simpa [A2, Finset.sum_const, nsmul_eq_mul] using
      (Finset.sum_filter (s := s) (p := P2) (f := fun _ => (1 : ℝ))).symm
  have hright :
      (∑ n ∈ s, (if P1 n then (1 : ℝ) else 0)) = (A1.card : ℝ) := by
    simpa [A1, Finset.sum_const, nsmul_eq_mul] using
      (Finset.sum_filter (s := s) (p := P1) (f := fun _ => (1 : ℝ))).symm
  have hcard : (A2.card : ℝ) ≤ (A1.card : ℝ) := by
    simpa [hleft, hright] using hsum_le
  -- Divide by |s| > 0
  have hscard_pos : 0 < (s.card : ℝ) := by exact_mod_cast hpos
  have hdiv :
      (A2.card : ℝ) / (s.card : ℝ) ≤ (A1.card : ℝ) / (s.card : ℝ) :=
    div_le_div_of_nonneg_right hcard (le_of_lt hscard_pos)
  -- Rewrite density definitions
  simpa [Sieve.MTCore.heavyDensity, s, A1, A2] using hdiv

end Stage3
end Sieve

