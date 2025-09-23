import Mathlib
import Sieve.Stage3TwinGap
import Sieve.Stage3PrimeFacade
import Sieve.AnalyticMocks

/-!
  Sieve/RunStage3TwinGapDemo.lean
  Minimal demo: specialize the k = 2 twin-window wrapper with the mock analytic input.
  This is a type-checking smoke test; it assumes an external hypothesis `h2`.
-/
noncomputable section
open Classical

example
  (W : Sieve.MaynardWeights.Weight) (τ : ℝ) (cfg : Sieve.MTCore.TupleConfig)
  (hne : (Sieve.MTCore.heavySet W τ).Nonempty)
  (h2 : (2 : ℝ) ≤ Sieve.Analytic.avgAsLower.lower W τ (([0, 2] : List ℤ).toFinset) (Sieve.Stage3.primeHS cfg)) :
  ∃ n : ℤ,
    2 ≤ Sieve.Stage3.windowHitCount (([0, 2] : List ℤ).toFinset)
          (Sieve.Stage3.hitIndicator (Sieve.Stage3.primeHS cfg)) n :=
  Sieve.Stage3TwinGap.exists_twin_window_with_two_primes_of_AI_ge_two_from_avg
    (AI := Sieve.Analytic.avgAsLower) (W := W) (τ := τ) (cfg := cfg) (hne := hne) (h2 := h2)
