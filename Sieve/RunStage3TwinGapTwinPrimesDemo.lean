import Mathlib
import Sieve.Stage3TwinGap
import Sieve.Stage3PrimesEndToEnd
import Sieve.AnalyticMocks

/-!
  Sieve/RunStage3TwinGapTwinPrimesDemo.lean
  Minimal demo: from an average lower bound ≥ 2 on the twin window (prime façade),
  deduce the existence of a twin prime pair.
-/
noncomputable section
open Classical

example
  (W : Sieve.MaynardWeights.Weight) (τ : ℝ) (cfg : Sieve.MTCore.TupleConfig)
  (hpos   : 0 < W.support.card)
  (hτleavg : τ ≤ (∑ m ∈ W.support, W.w m) / (W.support.card : ℝ))
  (h2 : (2 : ℝ) ≤ Sieve.Analytic.avgAsLower.lower W τ (([0, 2] : List ℤ).toFinset)
          (Sieve.Stage3.primeHS cfg)
          (Sieve.Stage3.heavySet_nonempty_of_avg_ge (W := W) (τ := τ) hpos hτleavg)) :
  ∃ p : ℤ, Sieve.Stage3.isPrimeZ p ∧ Sieve.Stage3.isPrimeZ (p + 2) :=
  Sieve.Stage3TwinGap.exists_twin_primes_of_AI_ge_two_from_avg
    (AI := Sieve.Analytic.avgAsLower) (W := W) (τ := τ) (cfg := cfg)
    (hpos := hpos) (hτleavg := hτleavg) (h2 := h2)
