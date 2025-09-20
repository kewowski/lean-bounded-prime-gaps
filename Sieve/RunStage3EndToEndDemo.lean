/-
  Sieve/RunStage3EndToEndDemo.lean
  End-to-end demo: assume avg(window hits) ≥ 1 on the heavy set,
  derive existence of a window hit via the AnalyticBridge + Stage3EndToEnd.
-/
import Sieve.Stage3EndToEnd

noncomputable section
open Classical BigOperators

example
    (W : Sieve.MaynardWeights.Weight) (τ : ℝ)
    (H : Finset ℤ) (HS : Sieve.Stage3.HitSystem)
    (hpos : 0 < W.support.card)
    (hτleavg :
      τ ≤ (∑ m ∈ W.support, W.w m) / (W.support.card : ℝ))
    (hAvg1 :
      1 ≤ Sieve.Stage3.avgOver (Sieve.MTCore.heavySet W τ)
            (Sieve.Stage3.windowSum H (Sieve.Stage3.hitIndicator HS))) :
    ∃ n ∈ Sieve.MTCore.heavySet W τ, ∃ h ∈ H, HS.isHit (n + h) := by
  classical
  -- Mock analytic input: set the "lower bound" equal to the actual average.
  let AI : Sieve.Analytic.AvgWindowHitLB :=
  { lower  := fun W τ H HS _hne =>
      Sieve.Stage3.avgOver (Sieve.MTCore.heavySet W τ)
        (Sieve.Stage3.windowSum H (Sieve.Stage3.hitIndicator HS))
    , le_avg := fun _ _ _ _ _ => le_of_eq rfl }
  -- Apply the end-to-end wrapper; h1 is exactly `hAvg1` under this AI.
  exact
    Sieve.Stage3.exists_hit_of_AI_ge_one_from_avg
      (AI := AI) (W := W) (τ := τ) (H := H) (HS := HS)
      (hpos := hpos) (hτleavg := hτleavg) (h1 := hAvg1)
