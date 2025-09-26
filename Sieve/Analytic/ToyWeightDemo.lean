/-
  Sieve/Analytic/ToyWeightDemo.lean
  A minimal concrete weight and simple facts:
  • toy weight W₀ with support {0}, w(0)=1, w(n≠0)=0,
  • heavySet W₀ τ is nonempty whenever τ ≤ 1,
  • sample use: heavy-card monotonicity in τ.
-/
import Mathlib
import Sieve.MTCore
import Sieve.MaynardWeights
import Sieve.Stage3HeavySetMonotone

noncomputable section
open Classical BigOperators

namespace Sieve.Analytic

/-- Underlying function for the toy weight. -/
private def w0fun (n : ℤ) : ℝ := if n = 0 then 1 else 0

/-- Tiny concrete weight: support {0}, mass 1 at 0, 0 elsewhere. -/
def W0 : Sieve.MaynardWeights.Weight where
  w        := w0fun
  support  := ({0} : Finset ℤ)
  nonneg   := by
    intro n; by_cases h : n = 0 <;> simp [w0fun, h]
  bounded  := by
    refine ⟨(1 : ℝ), ?_, ?_⟩
    · exact (by norm_num : 0 ≤ (1 : ℝ))
    · intro n; by_cases h : n = 0 <;> simp [w0fun, h, abs_one, abs_zero]
  -- These normalization flags are placeholders in this project.
  norm1    := True
  norm2    := True

@[simp] lemma W0_support : W0.support = ({0} : Finset ℤ) := rfl
@[simp] lemma W0_w_zero  : W0.w 0 = 1 := by simp [W0, w0fun]
@[simp] lemma W0_w_ne_zero {n : ℤ} (hn : n ≠ 0) : W0.w n = 0 := by simp [W0, w0fun, hn]

/-- Heavy set of `W0` at threshold `τ` is nonempty whenever `τ ≤ 1`. -/
lemma heavySet_W0_nonempty_of_tau_le_one {τ : ℝ} (h : τ ≤ 1) :
  (Sieve.MTCore.heavySet W0 τ).Nonempty := by
  classical
  -- `heavySet W τ = support.filter (fun n => τ ≤ w n)`
  have hmem : (0 : ℤ) ∈ Sieve.MTCore.heavySet W0 τ := by
    simp [Sieve.MTCore.heavySet, W0_support, W0_w_zero, h]
  exact ⟨0, hmem⟩

/-- Illustration: heavy-set cardinality is nonincreasing in τ for `W0`. -/
lemma heavy_card_mono_for_W0 {τ₁ τ₂ : ℝ} (hτ : τ₁ ≤ τ₂) :
  (Sieve.MTCore.heavySet W0 τ₂).card ≤ (Sieve.MTCore.heavySet W0 τ₁).card :=
  Sieve.Stage3.heavy_card_mono_in_tau (W := W0) hτ

end Sieve.Analytic
