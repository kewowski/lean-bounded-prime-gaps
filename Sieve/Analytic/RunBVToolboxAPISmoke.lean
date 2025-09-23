/-
  Sieve/Analytic/RunBVToolboxAPISmoke.lean
  UTF-8 (no BOM), ASCII-only.

  Purpose
  -------
  Smoke test for the *signatures-only* BV toolbox API:
  Given an abstract `api : BVToolboxAPI P` (no construction required),
  we package it into `AvgWindowHitLB` via `AvgWindowHitLB_of` and then
  apply the Stage-3 bridge lemma to deduce a hit from a ≥ 1 hypothesis.

  This keeps the demo assumption-driven and avoids any heavy proofs.
-/
import Mathlib
import Sieve.Analytic.BVToolboxAPI
import Sieve.AnalyticBridge

noncomputable section

namespace Sieve
namespace Analytic

/--
Smoke: with any `api : BVToolboxAPI P`, if the analytic lower bound at `(W,τ,H,HS)`
is ≥ 1, then there exists a heavy point whose window hits (Stage-3 façade).
-/
theorem toolbox_api_bridge_smoke
    (P : BVParams) (api : BVToolboxAPI P)
    (W : Sieve.MaynardWeights.Weight) (τ : ℝ)
    (H : Finset ℤ) (HS : Sieve.Stage3.HitSystem)
    (hne : (Sieve.MTCore.heavySet W τ).Nonempty)
    (h1 : 1 ≤ (AvgWindowHitLB_of P api).lower W τ H HS hne) :
    ∃ n ∈ Sieve.MTCore.heavySet W τ, ∃ k ∈ H, HS.isHit (n + k) := by
  -- Bridge lemma from Stage-3:
  exact
    exists_heavy_hit_of_lb_ge_one
      (AI := AvgWindowHitLB_of P api)
      (W := W) (τ := τ) (H := H) (HS := HS) (hne := hne) (h1 := h1)

/-- Availability sanity: the function compiles and can be referenced. -/
theorem toolbox_api_bridge_wired (P : BVParams) (_api : BVToolboxAPI P) : True := True.intro

end Analytic
end Sieve
