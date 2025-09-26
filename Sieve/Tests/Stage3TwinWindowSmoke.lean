import Mathlib
import Sieve.Stage3TwinGap
import Sieve.Analytic.BVMainStatement
import Sieve.Analytic.BVMainStatementWrapper
import Sieve.Analytic.RunTwinWindowFromBVMain

noncomputable section
open Classical

namespace Sieve.Tests

-- Indicator ↔ filtered-cardinality, instantiated.
example (HS : Sieve.Stage3.HitSystem) (H : Finset ℤ) (n : ℤ) :
  Sieve.Stage3.windowHitCount H HS n
    = ((H.filter (fun h => HS.isHit (n + h))).card : ℝ) :=
  Sieve.Stage3TwinGap.windowHitCount_eq_card_filter HS H n

-- Twin-window equivalence: card = 2 ↔ primes at n and n+2.
example (n : ℤ) :
  ((([0, 2] : List ℤ).toFinset).filter (fun h => Sieve.Stage3.isPrimeZ (n + h))).card = 2
    ↔ (Sieve.Stage3.isPrimeZ n ∧ Sieve.Stage3.isPrimeZ (n + 2)) :=
  Sieve.Stage3TwinGap.twin_window_card_eq_two_iff_twin_primes (n := n)

-- Nat→Real bridge for the prime façade.
example (cfg : Sieve.MTCore.TupleConfig) (n : ℤ)
  (hk : (2 : ℕ) ≤ ((([0, 2] : List ℤ).toFinset).filter (fun h => Sieve.Stage3.isPrimeZ (n + h))).card) :
  (2 : ℝ) ≤
    Sieve.Stage3.windowHitCount (([0, 2] : List ℤ).toFinset) (Sieve.Stage3.primeHS cfg) n :=
  Sieve.Stage3TwinGap.twinWindow_natCard_ge_two_implies_windowCount_ge_two
    (cfg := cfg) (n := n) hk

-- Analytic bridge: AI.lower ≥ 2 ⇒ ∃ twin-window with ≥ 2 hits.
example (AI : Sieve.Analytic.AvgWindowHitLB)
  (W : Sieve.MaynardWeights.Weight) (τ : ℝ) (cfg : Sieve.MTCore.TupleConfig)
  (hpos : 0 < W.support.card)
  (hτleavg : τ ≤ (∑ m ∈ W.support, W.w m) / (W.support.card : ℝ))
  (h2 :
    (2 : ℝ) ≤
      AI.lower W τ (([0, 2] : List ℤ).toFinset) (Sieve.Stage3.primeHS cfg)
        (Sieve.Stage3.heavySet_nonempty_of_avg_ge (W := W) (τ := τ) hpos hτleavg)) :
  ∃ n : ℤ,
    2 ≤ Sieve.Stage3.windowHitCount (([0, 2] : List ℤ).toFinset) (Sieve.Stage3.primeHS cfg) n :=
  Sieve.Stage3TwinGap.exists_twin_window_with_two_primes_of_AI_ge_two_from_avg
    (AI := AI) (W := W) (τ := τ) (cfg := cfg)
    (hpos := hpos) (hτleavg := hτleavg) (h2 := h2)

-- BV witness → twin-window existence (end-to-end).
example (P : Sieve.Analytic.BVParams) (TB : Sieve.Analytic.BVToolbox)
  (h : Sieve.Analytic.BVMainStatement P TB)
  (cfg : Sieve.MTCore.TupleConfig)
  (W : Sieve.MaynardWeights.Weight) (τ : ℝ)
  (hpos : 0 < W.support.card)
  (hτleavg : τ ≤ (∑ m ∈ W.support, W.w m) / (W.support.card : ℝ))
  (hLower2 : (2 : ℝ) ≤ Sieve.Analytic.lowerFormulaParams (P := P)) :
  ∃ n : ℤ,
    2 ≤ Sieve.Stage3.windowHitCount (([0, 2] : List ℤ).toFinset) (Sieve.Stage3.primeHS cfg) n :=
  Sieve.Analytic.exists_twin_window_from_BVMain
    (P := P) (TB := TB) (h := h) (cfg := cfg) (W := W) (τ := τ)
    (hpos := hpos) (hτleavg := hτleavg) (hLower2 := hLower2)

end Sieve.Tests
