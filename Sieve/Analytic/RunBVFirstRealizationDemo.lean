/-
  Sieve/Analytic/RunBVFirstRealizationDemo.lean
  UTF-8 (no BOM), ASCII-only.

  Demo: use `AI_first` with the Stage-3 bridge lemma.
  If `(AI_first TB).lower … ≥ 1`, then some heavy point’s window hits.
-/
import Mathlib
import Sieve.Analytic.BVFirstRealization
import Sieve.AnalyticBridge   -- demos may import the hub

noncomputable section

namespace Sieve
namespace Analytic

/-- From the toy AI, a ≥ 1 lower bound implies a hit in some heavy window. -/
theorem first_realization_demo
    (TB : BVToolboxProgressionsSig)
    (W : Sieve.MaynardWeights.Weight) (τ : ℝ)
    (H : Finset ℤ) (HS : Sieve.Stage3.HitSystem)
    (hne : (Sieve.MTCore.heavySet W τ).Nonempty)
    (h1 : 1 ≤ (AI_first TB).lower W τ H HS hne) :
    ∃ n ∈ Sieve.MTCore.heavySet W τ, ∃ k ∈ H, HS.isHit (n + k) := by
  -- Stage-3 bridge lemma
  exact
    exists_heavy_hit_of_lb_ge_one
      (AI := AI_first TB)
      (W := W) (τ := τ) (H := H) (HS := HS) (hne := hne) (h1 := h1)

/-- Touch `AI_first` so signature drift trips fast in CI. -/
theorem touch_ai_first (TB : BVToolboxProgressionsSig) : True := by
  let _ai : AvgWindowHitLB := AI_first TB
  exact True.intro

end Analytic
end Sieve
