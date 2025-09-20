/-
  Sieve/RunStage3PrimeCountsDemo.lean
  Smoke test for the real-threshold window-count extraction.
-/
import Sieve.Stage3Exports

noncomputable section
open Classical BigOperators

example
    (W : Sieve.MaynardWeights.Weight) (τ : ℝ) (H : Finset ℤ)
    (HS : Sieve.Stage3.HitSystem)
    (hne : (Sieve.MTCore.heavySet W τ).Nonempty)
    (t : ℝ)
    (hAvg :
      t ≤ Sieve.Stage3.avgOver (Sieve.MTCore.heavySet W τ)
            (Sieve.Stage3.windowSum H (Sieve.Stage3.hitIndicator HS))) :
    ∃ n ∈ Sieve.MTCore.heavySet W τ,
      t ≤ Sieve.Stage3.windowSum H (Sieve.Stage3.hitIndicator HS) n := by
  simpa using
    Sieve.Stage3.exists_heavy_with_hitcount_ge
      (W := W) (τ := τ) (H := H) (HS := HS) hne hAvg
