/-
  Sieve/Analytic/RunBVMainIneqDemo.lean
  UTF-8 (no BOM), ASCII-only.

  Purpose
  -------
  "Realized" bridge demo: given a single analytic inequality `BVMainIneq P`,
  we construct the Stage-3 interface `AvgWindowHitLB` via `AI_of_BV_ofIneq`,
  and immediately use the Stage-3 bridge lemma to deduce a hit when the
  lower bound is ≥ 1.

  Notes
  -----
  • This demo is *assumption-driven* (no heavy analysis here): we assume
    `BVMainIneq P` and a `≥ 1` hypothesis and thread them through.
  • Demos may import the Stage-3 bridge.
-/
import Mathlib
import Sieve.Analytic.Constants
import Sieve.Analytic.BVMainIneq
import Sieve.AnalyticBridge

noncomputable section

namespace Sieve
namespace Analytic

/--
Demo: from a provided analytic inequality `BVMainIneq P` and the hypothesis
`1 ≤ (AI_of_BV_ofIneq P h).lower …`, conclude existence of a heavy point
whose window contains a hit (via the Stage-3 bridge).
-/
theorem bridge_demo_exists_ofIneq
    (P : BVParams) (h : BVMainIneq P)
    (W : Sieve.MaynardWeights.Weight) (τ : ℝ)
    (H : Finset ℤ) (HS : Sieve.Stage3.HitSystem)
    (hne : (Sieve.MTCore.heavySet W τ).Nonempty)
    (h1 : 1 ≤ (AI_of_BV_ofIneq P h).lower W τ H HS hne) :
    ∃ n ∈ Sieve.MTCore.heavySet W τ, ∃ k ∈ H, HS.isHit (n + k) := by
  -- Use the Stage-3 bridge lemma with the *realized* analytic input.
  exact
    exists_heavy_hit_of_lb_ge_one
      (AI := AI_of_BV_ofIneq P h)
      (W := W) (τ := τ) (H := H) (HS := HS) (hne := hne) (h1 := h1)

/-- Sanity: the demo compiles and is available for any `P` once `BVMainIneq P` is given. -/
theorem bridge_demo_wired (P : BVParams) (_h : BVMainIneq P) : True := True.intro

end Analytic
end Sieve
