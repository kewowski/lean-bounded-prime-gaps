/-
  Sieve/RunStage3PrimeFacadeDemo.lean
  Smoke test for the prime-hit façade (abstract hits).
-/
import Sieve.Stage3Exports

noncomputable section
open Classical BigOperators

example
    (W : Sieve.MaynardWeights.Weight) (τ : ℝ)
    (H : Finset ℤ)
    (cfgH : Sieve.MTCore.TupleConfig)
    (hne : (Sieve.MTCore.heavySet W τ).Nonempty)
    -- Abstract hit system: say, "every n is a hit" (for a trivial demo)
    (HS : Sieve.Stage3.HitSystem := ⟨cfgH, fun _ => True⟩)
    -- Assume an average lower bound ≥ 1 for the indicator-window over the heavy set
    (hAvg :
      1 ≤ Sieve.Stage3.avgOver (Sieve.MTCore.heavySet W τ)
            (Sieve.Stage3.windowSum H (Sieve.Stage3.hitIndicator HS))) :
    ∃ n ∈ Sieve.MTCore.heavySet W τ, ∃ h ∈ H, HS.isHit (n + h) := by
  simpa using
    Sieve.Stage3.exists_heavy_with_hit_from_avg_ge_one
      (W := W) (τ := τ) (H := H) (HS := HS) hne hAvg
