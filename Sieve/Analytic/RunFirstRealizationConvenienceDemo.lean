/-
  Sieve/Analytic/RunFirstRealizationConvenienceDemo.lean
  UTF-8 (no BOM), ASCII-only.

  Demo: use the convenience one-liners to apply the Stage-3 bridge
  with `AI_first` and `AI_first_TB`.
-/
import Mathlib
import Sieve.Analytic.FirstRealizationConvenience

noncomputable section

namespace Sieve
namespace Analytic

/-- Convenience demo for `AI_first`. -/
theorem demo_convenience_ai_first
    (TB : BVToolboxProgressionsSig)
    (W : Sieve.MaynardWeights.Weight) (τ : ℝ)
    (H : Finset ℤ) (HS : Sieve.Stage3.HitSystem)
    (hne : (Sieve.MTCore.heavySet W τ).Nonempty)
    (h1 : 1 ≤ (AI_first TB).lower W τ H HS hne) :
    ∃ n ∈ Sieve.MTCore.heavySet W τ, ∃ k ∈ H, HS.isHit (n + k) :=
  exists_heavy_hit_of_ai_first_ge_one TB W τ H HS hne h1

/-- Convenience demo for `AI_first_TB`. -/
theorem demo_convenience_ai_first_TB
    (TB : BVToolboxProgressionsSig)
    (W : Sieve.MaynardWeights.Weight) (τ : ℝ)
    (H : Finset ℤ) (HS : Sieve.Stage3.HitSystem)
    (hne : (Sieve.MTCore.heavySet W τ).Nonempty)
    (h1 : 1 ≤ (AI_first_TB TB).lower W τ H HS hne) :
    ∃ n ∈ Sieve.MTCore.heavySet W τ, ∃ k ∈ H, HS.isHit (n + k) :=
  exists_heavy_hit_of_ai_first_TB_ge_one TB W τ H HS hne h1

end Analytic
end Sieve
