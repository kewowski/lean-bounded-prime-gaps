/-
  Sieve/RunAnalyticBVTemplateDemo.lean
  Minimal type-check demo for the BV/EH template plugged into Stage-3 wrappers.
-/
import Mathlib
import Sieve.AnalyticBVTemplate
import Sieve.Stage3PrimesEndToEnd
import Sieve.Stage3TwinGap

noncomputable section
open Classical

example
  (W : Sieve.MaynardWeights.Weight) (τ : ℝ) (cfg : Sieve.MTCore.TupleConfig)
  (hpos   : 0 < W.support.card)
  (hτleavg : τ ≤ (∑ m ∈ W.support, W.w m) / (W.support.card : ℝ))
  -- Hypothetical analytic lower bounds (to be provided by real BV/EH work):
  (h1 : (1 : ℝ) ≤ Sieve.Analytic.bvTemplateAsLower.lower W τ
          (([0, 2] : List ℤ).toFinset) (Sieve.Stage3.primeHS cfg)
          (Sieve.Stage3.heavySet_nonempty_of_avg_ge (W := W) (τ := τ) hpos hτleavg))
  (h2 : (2 : ℝ) ≤ Sieve.Analytic.bvTemplateAsLower.lower W τ
          (([0, 2] : List ℤ).toFinset) (Sieve.Stage3.primeHS cfg)
          (Sieve.Stage3.heavySet_nonempty_of_avg_ge (W := W) (τ := τ) hpos hτleavg)) :
  (∃ n ∈ Sieve.MTCore.heavySet W τ, ∃ h ∈ (([0, 2] : List ℤ).toFinset), Sieve.Stage3.isPrimeZ (n + h))
  ∧ (∃ p, Sieve.Stage3.isPrimeZ p ∧ Sieve.Stage3.isPrimeZ (p + 2)) :=
by
  refine ⟨?primeInTwinWindow, ?twinPair⟩
  · -- ≥1 ⇒ some prime in the twin window
    exact
      Sieve.Stage3.exists_prime_in_twin_window_of_AI_ge_one_from_avg
        (AI := Sieve.Analytic.bvTemplateAsLower)
        (W := W) (τ := τ) (cfg := cfg)
        (hpos := hpos) (hτleavg := hτleavg) (h1 := h1)
  · -- ≥2 ⇒ a twin prime pair
    exact
      Sieve.Stage3TwinGap.exists_twin_primes_of_AI_ge_two_from_avg
        (AI := Sieve.Analytic.bvTemplateAsLower)
        (W := W) (τ := τ) (cfg := cfg)
        (hpos := hpos) (hτleavg := hτleavg) (h2 := h2)
