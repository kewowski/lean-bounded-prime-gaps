/-
  Sieve/Analytic/RunBVPiecesBridgeSmoke.lean
  UTF-8 (no BOM), ASCII-only.

  Purpose
  -------
  Smoke that uses the new `BVBridgePieces` + `BVToolboxProgressionsSig`
  to build an `AvgWindowHitLB` via `AvgWindowHitLB_fromPieces`, and then
  applies the Stage-3 bridge lemma. Assumption-driven, no heavy analysis.

  This ensures the new derivation skeleton is actually consumable by Stage-3.
-/
import Mathlib
import Sieve.Analytic.BVMainDeriveFromToolbox
import Sieve.AnalyticBridge

noncomputable section

namespace Sieve
namespace Analytic

/--
Smoke: with toolbox signatures `TB` and bridge payload `bp`, package them into
`AvgWindowHitLB` and use the Stage-3 bridge lemma to deduce a hit from a ≥ 1 hypothesis.
-/
theorem bridge_from_pieces_smoke
    (P : BVParams) (TB : BVToolboxProgressionsSig) (bp : BVBridgePieces P)
    (W : Sieve.MaynardWeights.Weight) (τ : ℝ)
    (H : Finset ℤ) (HS : Sieve.Stage3.HitSystem)
    (hne : (Sieve.MTCore.heavySet W τ).Nonempty)
    (h1 : 1 ≤ (AvgWindowHitLB_fromPieces P TB bp).lower W τ H HS hne) :
    ∃ n ∈ Sieve.MTCore.heavySet W τ, ∃ k ∈ H, HS.isHit (n + k) := by
  exact
    exists_heavy_hit_of_lb_ge_one
      (AI := AvgWindowHitLB_fromPieces P TB bp)
      (W := W) (τ := τ) (H := H) (HS := HS) (hne := hne) (h1 := h1)

/-- Availability sanity: references compile and are usable. -/
theorem bridge_from_pieces_wired
    (P : BVParams) (_TB : BVToolboxProgressionsSig) (_bp : BVBridgePieces P) : True :=
  True.intro

end Analytic
end Sieve
