/-
  Sieve/Analytic/RunBVBridgeSmoke.lean
  UTF-8 (no BOM), ASCII-only.

  Purpose
  -------
  Tiny smoke theorem that *uses* our current wiring `AI_of_BV` together with
  the Stage-3 bridge lemma `exists_heavy_hit_of_lb_ge_one`. This keeps the
  demo purely type-level and algebraic: we assume the `≥ 1` hypothesis and
  pass it through the bridge.

  Notes
  -----
  • Demos are allowed to import the Stage-3 hub/bridge.
  • No heavy analysis here; just plumbing validation.
-/
import Mathlib
import Sieve.Analytic.Constants
import Sieve.Analytic.BVMainAssumptions
import Sieve.Analytic.BVMainStatementWire
import Sieve.AnalyticBridge

noncomputable section

namespace Sieve
namespace Analytic

/--
Smoke bridge: from `1 ≤ (AI_of_BV P A).lower …` conclude the existence of a heavy point
whose window contains a hit (Stage-3 façade).
-/
theorem bridge_demo_exists
    (P : BVParams) (A : BVMainAssumptions P)
    (W : Sieve.MaynardWeights.Weight) (τ : ℝ)
    (H : Finset ℤ) (HS : Sieve.Stage3.HitSystem)
    (hne : (Sieve.MTCore.heavySet W τ).Nonempty)
    (h1 : 1 ≤ (AI_of_BV P A).lower W τ H HS hne) :
    ∃ n ∈ Sieve.MTCore.heavySet W τ, ∃ h ∈ H, HS.isHit (n + h) := by
  -- Directly apply the Stage-3 bridge lemma:
  simpa using
    (exists_heavy_hit_of_lb_ge_one
      (AI := AI_of_BV P A) (W := W) (τ := τ) (H := H) (HS := HS)
      (hne := hne) (h1 := h1))

end Analytic
end Sieve
