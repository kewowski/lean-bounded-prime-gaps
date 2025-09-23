/-
  Sieve/RunBVMainStatementDemo.lean
  Demo: given `h : BVMainStatement P TB`, build `AI := AI_of_BV P TB h`
  and derive ≥1 / ≥2 consequences in the twin window.
-/
import Mathlib
import Sieve.Analytic.BVMainStatement
import Sieve.Stage3PrimesEndToEnd
import Sieve.Stage3TwinGap

noncomputable section
open Classical

/-- If `BVMainStatement` holds and the lower bound is ≥ 1 on `{0,2}`,
we can extract a prime in the twin window. -/
example
  (P : Sieve.Analytic.BVParams) (TB : Sieve.Analytic.BVToolbox)
  (h : Sieve.Analytic.BVMainStatement P TB)
  (W : Sieve.MaynardWeights.Weight) (τ : ℝ) (cfg : Sieve.MTCore.TupleConfig)
  (hpos   : 0 < W.support.card)
  (hτleavg : τ ≤ (∑ m ∈ W.support, W.w m) / (W.support.card : ℝ))
  (h1 :
    (1 : ℝ) ≤
      (Sieve.Analytic.AI_of_BV P TB h).lower W τ
        (([0, 2] : List ℤ).toFinset) (Sieve.Stage3.primeHS cfg)
        (Sieve.Stage3.heavySet_nonempty_of_avg_ge (W := W) (τ := τ) hpos hτleavg)) :
  ∃ n ∈ Sieve.MTCore.heavySet W τ, ∃ h ∈ (([0, 2] : List ℤ).toFinset), Sieve.Stage3.isPrimeZ (n + h) := by
  classical
  let AI := Sieve.Analytic.AI_of_BV P TB h
  simpa using
    Sieve.Stage3.exists_prime_in_twin_window_of_AI_ge_one_from_avg
      (AI := AI) (W := W) (τ := τ) (cfg := cfg)
      (hpos := hpos) (hτleavg := hτleavg) (h1 := h1)

/-- If `BVMainStatement` holds and the lower bound is ≥ 2 on `{0,2}`,
we can extract a twin prime pair. -/
example
  (P : Sieve.Analytic.BVParams) (TB : Sieve.Analytic.BVToolbox)
  (h : Sieve.Analytic.BVMainStatement P TB)
  (W : Sieve.MaynardWeights.Weight) (τ : ℝ) (cfg : Sieve.MTCore.TupleConfig)
  (hpos   : 0 < W.support.card)
  (hτleavg : τ ≤ (∑ m ∈ W.support, W.w m) / (W.support.card : ℝ))
  (h2 :
    (2 : ℝ) ≤
      (Sieve.Analytic.AI_of_BV P TB h).lower W τ
        (([0, 2] : List ℤ).toFinset) (Sieve.Stage3.primeHS cfg)
        (Sieve.Stage3.heavySet_nonempty_of_avg_ge (W := W) (τ := τ) hpos hτleavg)) :
  ∃ p : ℤ, Sieve.Stage3.isPrimeZ p ∧ Sieve.Stage3.isPrimeZ (p + 2) := by
  classical
  let AI := Sieve.Analytic.AI_of_BV P TB h
  simpa using
    Sieve.Stage3TwinGap.exists_twin_primes_of_AI_ge_two_from_avg
      (AI := AI) (W := W) (τ := τ) (cfg := cfg)
      (hpos := hpos) (hτleavg := hτleavg) (h2 := h2)
