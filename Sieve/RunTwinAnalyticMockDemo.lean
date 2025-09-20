/-
  Sieve/RunTwinAnalyticMockDemo.lean
  Demo: use AnalyticInputs.avgAsLower to conclude a prime in the twin window {0,2}
  from the assumption avg(window prime-hits) ≥ 1 on the heavy set.
-/
import Sieve.Stage3PrimesEndToEnd
import Sieve.AnalyticMocks

noncomputable section
open Classical BigOperators

example
    (W : Sieve.MaynardWeights.Weight) (τ : ℝ)
    (cfg : Sieve.MTCore.TupleConfig)  -- carried by primeHS
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
  -- Use the shared mock analytic input: lower bound = actual average
  simpa using
    Sieve.Stage3.exists_prime_in_twin_window_of_AI_ge_one_from_avg
      (AI := Sieve.AnalyticInputs.avgAsLower)
      (W := W) (τ := τ) (cfg := cfg)
      (hpos := hpos) (hτleavg := hτleavg) (h1 := hAvg1)
