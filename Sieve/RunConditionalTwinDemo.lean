/-
  Sieve/RunConditionalTwinDemo.lean
  Demo: use the conditional twin wrapper with the mock analytic input.
-/
import Sieve.ConditionalTwin
import Sieve.AnalyticMocks

noncomputable section
open Classical BigOperators

example
    (W : Sieve.MaynardWeights.Weight) (τ : ℝ)
    (cfg : Sieve.MTCore.TupleConfig)
    (hpos : 0 < W.support.card)
    (hτleavg :
      τ ≤ (∑ m ∈ W.support, W.w m) / (W.support.card : ℝ))
    (hAvg1 :
      1 ≤ Sieve.Stage3.avgOver (Sieve.MTCore.heavySet W τ)
            (Sieve.Stage3.windowSum (([0, 2] : List ℤ).toFinset)
              (Sieve.Stage3.hitIndicator (Sieve.Stage3.primeHS cfg)))) :
    ∃ n ∈ Sieve.MTCore.heavySet W τ,
      ∃ h ∈ (([0, 2] : List ℤ).toFinset), Sieve.Stage3.isPrimeZ (n + h) := by
  classical
  -- Apply the conditional wrapper with the mock analytic input:
  simpa using
    Sieve.Conditional.twin_of_AI_ge_one_from_avg
      (AI := Sieve.AnalyticInputs.avgAsLower)
      (W := W) (τ := τ) (cfg := cfg)
      (hpos := hpos) (hτleavg := hτleavg) (h1 := hAvg1)
