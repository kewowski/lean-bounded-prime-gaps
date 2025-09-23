/-
  Sieve/Analytic/RunBVFirstAverageNonnegDemo.lean
  UTF-8 (no BOM), ASCII-only.

  Demo: show explicitly that the heavy-set average of the 0/1 window indicator
  is ≥ 0 (nonnegativity argument), and thread it through `AI_first` so that the
  shape matches the gateway inequality.
-/
import Mathlib
import Sieve.Stage3Window
import Sieve.Stage3PrimeFacade
import Sieve.Analytic.BVFirstRealization   -- P₀, avgOver_nonneg_of_nonneg, windowSum_hitIndicator_nonneg

noncomputable section

namespace Sieve
namespace Analytic

/-- Heavy-set average of a 0/1 window indicator is nonnegative. -/
theorem avg_heavy_window_indicator_nonneg
    (W : Sieve.MaynardWeights.Weight) (τ : ℝ)
    (H : Finset ℤ) (HS : Sieve.Stage3.HitSystem)
    (hne : (Sieve.MTCore.heavySet W τ).Nonempty) :
    0 ≤ Sieve.Stage3.avgOver (Sieve.MTCore.heavySet W τ)
          (Sieve.Stage3.windowSum H (Sieve.Stage3.hitIndicator HS)) := by
  -- pointwise nonnegativity → average nonnegativity
  have hpt :
      ∀ n ∈ Sieve.MTCore.heavySet W τ,
        0 ≤ Sieve.Stage3.windowSum H (Sieve.Stage3.hitIndicator HS) n := by
    intro n _; exact windowSum_hitIndicator_nonneg H HS n
  exact
    avgOver_nonneg_of_nonneg
      (A := Sieve.MTCore.heavySet W τ)
      (g := Sieve.Stage3.windowSum H (Sieve.Stage3.hitIndicator HS))
      hne hpt

/-- Thread the same fact through `AI_first`, matching the gateway inequality’s shape. -/
theorem ai_first_gateway_nonneg
    (TB : BVToolboxProgressionsSig)
    (W : Sieve.MaynardWeights.Weight) (τ : ℝ)
    (H : Finset ℤ) (HS : Sieve.Stage3.HitSystem)
    (hne : (Sieve.MTCore.heavySet W τ).Nonempty) :
    BVParams.lowerFormula P₀
      ≤ Sieve.Stage3.avgOver (Sieve.MTCore.heavySet W τ)
            (Sieve.Stage3.windowSum H (Sieve.Stage3.hitIndicator HS)) := by
  -- Touch TB so it isn't considered unused (keeps the surface “hot”).
  let _ := TB.C_LS
  -- In `P₀`, the lower formula is 0.
  have h0 : BVParams.lowerFormula P₀ = 0 := P₀_lowerFormula
  -- Close with the nonnegativity lemma.
  have h := avg_heavy_window_indicator_nonneg W τ H HS hne
  simpa [h0] using h

end Analytic
end Sieve
