/-
  Sieve/Analytic/AvgFromFirstMoment.lean

  Turn a first-moment (sum) lower bound into an average lower bound.
  Leaf-only, linter-friendly helpers with a heavy-set specialization.
-/
import Mathlib
import Sieve.Stage3Window
import Sieve.Stage3

noncomputable section
open Classical

namespace Sieve
namespace Analytic

/-- If `A` is nonempty and `(A.card : ℝ) * c ≤ ∑_{a∈A} f a`, then `c ≤ avgOver A f`. -/
lemma avgOver_ge_of_sum_ge
    {A : Finset ℤ} (hA : A.Nonempty) (f : ℤ → ℝ) (c : ℝ)
    (h : (A.card : ℝ) * c ≤ ∑ a ∈ A, f a) :
    c ≤ Sieve.Stage3.avgOver A f := by
  classical
  have hpos : 0 < (A.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hA
  -- Divide both sides of h by |A| (positive), then simplify the left.
  have hdiv :
      ((A.card : ℝ) * c) / (A.card : ℝ)
        ≤ (∑ a ∈ A, f a) / (A.card : ℝ) :=
    div_le_div_of_nonneg_right h (le_of_lt hpos)
  have hne : (A.card : ℝ) ≠ 0 := ne_of_gt hpos
  have hleft :
      ((A.card : ℝ) * c) / (A.card : ℝ) = c := by
    calc
      ((A.card : ℝ) * c) / (A.card : ℝ)
          = (c * (A.card : ℝ)) / (A.card : ℝ) := by simp [mul_comm]
      _ = c * ((A.card : ℝ) / (A.card : ℝ)) := by simp [mul_div_assoc]
      _ = c := by simp [div_self hne]
  have : c ≤ (∑ a ∈ A, f a) / (A.card : ℝ) := by
    simpa [hleft] using hdiv
  simpa [Sieve.Stage3.avgOver] using this

/-- Heavy-set specialization. If `heavy` is nonempty and its sum is ≥ c·|heavy|,
    then the heavy-set average is ≥ c. -/
lemma avgOver_heavy_ge_of_sum_ge
    (W : Sieve.MaynardWeights.Weight) (τ : ℝ)
    (H : Finset ℤ) (HS : Sieve.Stage3.HitSystem)
    (hne : (Sieve.MTCore.heavySet W τ).Nonempty)
    (c : ℝ)
    (h : ((Sieve.MTCore.heavySet W τ).card : ℝ) * c
           ≤ ∑ n ∈ Sieve.MTCore.heavySet W τ,
                Sieve.Stage3.windowSum H (Sieve.Stage3.hitIndicator HS) n) :
    c ≤ Sieve.Stage3.avgOver (Sieve.MTCore.heavySet W τ)
           (Sieve.Stage3.windowSum H (Sieve.Stage3.hitIndicator HS)) := by
  classical
  -- Apply the generic lemma with A = heavySet, f = windowSum H hitIndicator
  exact avgOver_ge_of_sum_ge (A := Sieve.MTCore.heavySet W τ)
          (hA := hne) (f := Sieve.Stage3.windowSum H (Sieve.Stage3.hitIndicator HS))
          (c := c) (h := h)

end Analytic
end Sieve
