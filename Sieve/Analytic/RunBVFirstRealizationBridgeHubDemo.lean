/-
  Sieve/Analytic/RunBVFirstRealizationBridgeHubDemo.lean
  UTF-8 (no BOM), ASCII-only.

  Demo: use the BridgeHub alias `AvgWindowHitLBFromPieces` with our toy pieces `P₀, bp₀`.
  If `(AvgWindowHitLBFromPieces P₀ TB bp₀).lower … ≥ 1`, then some heavy point’s window hits.
-/
import Mathlib
import Sieve.Analytic.BridgeHub          -- hub (demos may import hubs)
import Sieve.Analytic.BVFirstRealization -- P₀ and bp₀

noncomputable section

namespace Sieve
namespace Analytic

/-- Hub-flavored demo: ≥ 1 lower bound ⇒ a heavy-window hit. -/
theorem bridge_hub_demo_first
    (TB : BVToolboxProgressionsSig)
    (W : Sieve.MaynardWeights.Weight) (τ : ℝ)
    (H : Finset ℤ) (HS : Sieve.Stage3.HitSystem)
    (hne : (Sieve.MTCore.heavySet W τ).Nonempty)
    (h1 :
      1 ≤ (AvgWindowHitLBFromPieces P₀ TB bp₀).lower W τ H HS hne) :
    ∃ n ∈ Sieve.MTCore.heavySet W τ, ∃ k ∈ H, HS.isHit (n + k) := by
  exact
    exists_heavy_hit_of_lb_ge_one
      (AI := AvgWindowHitLBFromPieces P₀ TB bp₀)
      (W := W) (τ := τ) (H := H) (HS := HS) (hne := hne) (h1 := h1)

end Analytic
end Sieve
