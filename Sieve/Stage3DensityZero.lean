/-
  Sieve/Stage3DensityZero.lean
  When the support is nonempty, heavy density = 0 ↔ heavy set is empty.
-/
import Mathlib
import Sieve.MTCore

noncomputable section
open Classical BigOperators

namespace Sieve
namespace Stage3

/-- If the support is nonempty, then `heavyDensity = 0 ↔ heavySet = ∅`. -/
theorem heavyDensity_zero_iff_heavySet_empty
    (W : Sieve.MaynardWeights.Weight) (τ : ℝ)
    (hpos : 0 < W.support.card) :
    Sieve.MTCore.heavyDensity W τ = 0
      ↔ Sieve.MTCore.heavySet W τ = ∅ := by
  classical
  set s : Finset ℤ := W.support
  set P : ℤ → Prop := fun n => τ ≤ W.w n
  set A : Finset ℤ := s.filter P
  have hscard_pos : 0 < (s.card : ℝ) := by exact_mod_cast hpos
  have hscard_ne  : (s.card : ℝ) ≠ 0 := ne_of_gt hscard_pos
  constructor
  · -- density = 0 ⇒ numerator = 0 ⇒ heavy set empty
    intro h0
    have hdiv0 : (A.card : ℝ) / (s.card : ℝ) = 0 := by
      simpa [Sieve.MTCore.heavyDensity, s, A, P] using h0
    -- multiply both sides by |s|; simplify to (A.card : ℝ) = 0
    have hmul := congrArg (fun x : ℝ => x * (s.card : ℝ)) hdiv0
    have hA0 : (A.card : ℝ) = 0 := by
      -- `simp` handles `((a/b)*b)` using `div_eq_mul_inv` and `hscard_ne`
      have hden : (s.card : ℝ) ≠ 0 := hscard_ne
      simp [div_eq_mul_inv, hden] at hmul
      simpa using hmul
    -- cast back and conclude emptiness
    have hAcard0 : A.card = 0 := by exact_mod_cast hA0
    have hAempty : A = ∅ := Finset.card_eq_zero.mp hAcard0
    simpa [Sieve.MTCore.heavySet, s, A, P] using hAempty
  · -- heavy set empty ⇒ density = 0
    intro hAempty
    simp [Sieve.MTCore.heavyDensity, Sieve.MTCore.heavySet, hAempty]

end Stage3
end Sieve


