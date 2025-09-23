/-
  Sieve/RunBVSketchTwinDemo.lean
  Demo: assume a proof that `lowerFormula ≤ avgOver(...)`, build `AI := bvSketch`,
  and show the Stage-3 consequences (≥1 ⇒ a prime in the twin window; ≥2 ⇒ twin primes).

  Updated: `P : ℝ` so the lower bound is a meaningful constant.
-/
import Mathlib
import Sieve.Analytic.BVSketch
import Sieve.Stage3PrimesEndToEnd
import Sieve.Stage3TwinGap

noncomputable section
open Classical

/-- If the analytic inequality holds and the lower bound is ≥ 1 on `{0,2}`,
we can extract a prime in the twin window. -/
example
  (P : ℝ) (TB : Sieve.Analytic.BVToolbox)
  (proof :
    ∀ (W : Sieve.MaynardWeights.Weight) (τ : ℝ)
      (H : Finset ℤ) (HS : Sieve.Stage3.HitSystem)
      (hne : (Sieve.MTCore.heavySet W τ).Nonempty),
      Sieve.Analytic.lowerFormula P W τ H HS hne
        ≤ Sieve.Stage3.avgOver (Sieve.MTCore.heavySet W τ)
            (Sieve.Stage3.windowSum H (Sieve.Stage3.hitIndicator HS)))
  (W : Sieve.MaynardWeights.Weight) (τ : ℝ) (cfg : Sieve.MTCore.TupleConfig)
  (hpos   : 0 < W.support.card)
  (hτleavg : τ ≤ (∑ m ∈ W.support, W.w m) / (W.support.card : ℝ))
  (h1 :
    (1 : ℝ) ≤
      (Sieve.Analytic.bvSketch P TB proof).lower W τ
        (([0, 2] : List ℤ).toFinset) (Sieve.Stage3.primeHS cfg)
        (Sieve.Stage3.heavySet_nonempty_of_avg_ge (W := W) (τ := τ) hpos hτleavg)) :
  ∃ n ∈ Sieve.MTCore.heavySet W τ, ∃ h ∈ (([0, 2] : List ℤ).toFinset), Sieve.Stage3.isPrimeZ (n + h) := by
  classical
  let AI := Sieve.Analytic.bvSketch P TB proof
  simpa using
    Sieve.Stage3.exists_prime_in_twin_window_of_AI_ge_one_from_avg
      (AI := AI) (W := W) (τ := τ) (cfg := cfg)
      (hpos := hpos) (hτleavg := hτleavg) (h1 := h1)

/-- If the analytic inequality holds and the lower bound is ≥ 2 on `{0,2}`,
we can extract a twin prime pair. -/
example
  (P : ℝ) (TB : Sieve.Analytic.BVToolbox)
  (proof :
    ∀ (W : Sieve.MaynardWeights.Weight) (τ : ℝ)
      (H : Finset ℤ) (HS : Sieve.Stage3.HitSystem)
      (hne : (Sieve.MTCore.heavySet W τ).Nonempty),
      Sieve.Analytic.lowerFormula P W τ H HS hne
        ≤ Sieve.Stage3.avgOver (Sieve.MTCore.heavySet W τ)
            (Sieve.Stage3.windowSum H (Sieve.Stage3.hitIndicator HS)))
  (W : Sieve.MaynardWeights.Weight) (τ : ℝ) (cfg : Sieve.MTCore.TupleConfig)
  (hpos   : 0 < W.support.card)
  (hτleavg : τ ≤ (∑ m ∈ W.support, W.w m) / (W.support.card : ℝ))
  (h2 :
    (2 : ℝ) ≤
      (Sieve.Analytic.bvSketch P TB proof).lower W τ
        (([0, 2] : List ℤ).toFinset) (Sieve.Stage3.primeHS cfg)
        (Sieve.Stage3.heavySet_nonempty_of_avg_ge (W := W) (τ := τ) hpos hτleavg)) :
  ∃ p : ℤ, Sieve.Stage3.isPrimeZ p ∧ Sieve.Stage3.isPrimeZ (p + 2) := by
  classical
  let AI := Sieve.Analytic.bvSketch P TB proof
  simpa using
    Sieve.Stage3TwinGap.exists_twin_primes_of_AI_ge_two_from_avg
      (AI := AI) (W := W) (τ := τ) (cfg := cfg)
      (hpos := hpos) (hτleavg := hτleavg) (h2 := h2)
