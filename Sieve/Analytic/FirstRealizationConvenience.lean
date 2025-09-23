/-
  Sieve/Analytic/FirstRealizationConvenience.lean
  UTF-8 (no BOM), ASCII-only.

  Convenience wrappers for using the toy AI realizations (`AI_first`, `AI_first_TB`)
  with the Stage-3 bridge lemma. These keep downstream code terse and stable.
-/
import Mathlib
import Sieve.Analytic.BVFirstRealization
import Sieve.Analytic.BVFirstRealizationTB
import Sieve.AnalyticBridge   -- demos may import the hub

noncomputable section

namespace Sieve
namespace Analytic

/-- One-liner: with `AI_first`, a ≥ 1 lower bound implies a heavy-window hit. -/
theorem exists_heavy_hit_of_ai_first_ge_one
    (TB : BVToolboxProgressionsSig)
    (W : Sieve.MaynardWeights.Weight) (τ : ℝ)
    (H : Finset ℤ) (HS : Sieve.Stage3.HitSystem)
    (hne : (Sieve.MTCore.heavySet W τ).Nonempty)
    (h1 : 1 ≤ (AI_first TB).lower W τ H HS hne) :
    ∃ n ∈ Sieve.MTCore.heavySet W τ, ∃ k ∈ H, HS.isHit (n + k) :=
  exists_heavy_hit_of_lb_ge_one
    (AI := AI_first TB)
    (W := W) (τ := τ) (H := H) (HS := HS) (hne := hne) (h1 := h1)

/-- Same, but for the toolbox-threaded variant `AI_first_TB`. -/
theorem exists_heavy_hit_of_ai_first_TB_ge_one
    (TB : BVToolboxProgressionsSig)
    (W : Sieve.MaynardWeights.Weight) (τ : ℝ)
    (H : Finset ℤ) (HS : Sieve.Stage3.HitSystem)
    (hne : (Sieve.MTCore.heavySet W τ).Nonempty)
    (h1 : 1 ≤ (AI_first_TB TB).lower W τ H HS hne) :
    ∃ n ∈ Sieve.MTCore.heavySet W τ, ∃ k ∈ H, HS.isHit (n + k) :=
  exists_heavy_hit_of_lb_ge_one
    (AI := AI_first_TB TB)
    (W := W) (τ := τ) (H := H) (HS := HS) (hne := hne) (h1 := h1)

end Analytic
end Sieve
