/-
  Sieve/RunTwinEndToEndDemo.lean
  End-to-end twin demo: assuming avg(window prime-hits) ≥ 1 on the heavy set,
  produce a prime in the twin window {0,2}.
-/
import Sieve.Stage3PrimesEndToEnd

noncomputable section
open Classical BigOperators

example
    (W : Sieve.MaynardWeights.Weight) (τ : ℝ)
    (cfg : Sieve.MTCore.TupleConfig)  -- arbitrary tuple config; carried by `primeHS`
    (hpos : 0 < W.support.card)
    (hτleavg :
      τ ≤ (∑ m ∈ W.support, W.w m) / (W.support.card : ℝ))
    (hAvg1 :
      1 ≤ Sieve.Stage3.avgOver (Sieve.MTCore.heavySet W τ)
            (Sieve.Stage3.windowSum (([0, 2] : List ℤ).toFinset)
              (Sieve.Stage3.hitIndicator (Sieve.Stage3.primeHS cfg)))) :
    ∃ n ∈ Sieve.MTCore.heavySet W τ, ∃ h ∈ (([0, 2] : List ℤ).toFinset),
      Sieve.Stage3.isPrimeZ (n + h) := by
  classical
  -- Mock analytic input: set "lower bound" = actual average
  let AI : Sieve.Analytic.AvgWindowHitLB :=
  { lower  := fun W τ H HS _hne =>
      Sieve.Stage3.avgOver (Sieve.MTCore.heavySet W τ)
        (Sieve.Stage3.windowSum H (Sieve.Stage3.hitIndicator HS))
    , le_avg := fun _ _ _ _ _ => le_of_eq rfl }
  -- Apply prime-specialized end-to-end wrapper with H = {0,2}
  simpa using
    Sieve.Stage3.exists_prime_in_window_of_AI_ge_one_from_avg
      (AI := AI) (W := W) (τ := τ)
      (H := (([0, 2] : List ℤ).toFinset))
      (cfg := cfg)
      (hpos := hpos) (hτleavg := hτleavg) (h1 := hAvg1)
