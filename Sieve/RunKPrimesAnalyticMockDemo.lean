/-
  Sieve/RunKPrimesAnalyticMockDemo.lean
  Demo: with AnalyticInputs.avgAsLower and avg ≥ k, conclude ≥ k primes in window H.
-/
import Sieve.Stage3PrimesEndToEnd
import Sieve.AnalyticMocks

noncomputable section
open Classical BigOperators

example
    (W : Sieve.MaynardWeights.Weight) (τ : ℝ)
    (cfg : Sieve.MTCore.TupleConfig)
    (H : Finset ℤ) (k : ℕ)
    (hpos : 0 < W.support.card)
    (hτleavg :
      τ ≤ (∑ m ∈ W.support, W.w m) / (W.support.card : ℝ))
    (hAvgK :
      (k : ℝ) ≤ Sieve.Stage3.avgOver (Sieve.MTCore.heavySet W τ)
            (Sieve.Stage3.windowSum H (Sieve.Stage3.hitIndicator (Sieve.Stage3.primeHS cfg)))) :
    ∃ n ∈ Sieve.MTCore.heavySet W τ,
      k ≤ (H.filter (fun h => Sieve.Stage3.isPrimeZ (n + h))).card := by
  classical
  -- Use the mock analytic input: lower bound = actual average
  simpa using
    Sieve.Stage3.exists_atLeast_k_primes_in_window_of_AI_ge_k_from_avg
      (AI := Sieve.AnalyticInputs.avgAsLower)
      (W := W) (τ := τ) (H := H) (cfg := cfg)
      (hpos := hpos) (hτleavg := hτleavg) (k := k) (hk := hAvgK)
