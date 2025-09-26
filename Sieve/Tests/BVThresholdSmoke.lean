import Mathlib
import Sieve.Analytic.RunTwinWindowFromBVThreshold

noncomputable section
open Classical

namespace Sieve.Tests

-- If BV main statement holds, and P meets its threshold with 2 ≤ threshold,
-- then we can produce an n with ≥ 2 hits in the twin window.
example
  (P : Sieve.Analytic.BVParams) (TB : Sieve.Analytic.BVToolbox)
  (h : Sieve.Analytic.BVMainStatement P TB)
  (cfg : Sieve.MTCore.TupleConfig)
  (W : Sieve.MaynardWeights.Weight) (τ : ℝ)
  (hpos : 0 < W.support.card)
  (hτleavg : τ ≤ (∑ m ∈ W.support, W.w m) / (W.support.card : ℝ))
  (hMeet : Sieve.Analytic.meetsThreshold P)
  (hTwoLe : (2 : ℝ) ≤ P.threshold) :
  ∃ n : ℤ,
    2 ≤
      Sieve.Stage3.windowHitCount (([0, 2] : List ℤ).toFinset)
        (Sieve.Stage3.primeHS cfg) n :=
by
  simpa using
    Sieve.Analytic.exists_twin_window_from_BVMain_threshold
      (P := P) (TB := TB) (h := h) (cfg := cfg) (W := W) (τ := τ)
      (hpos := hpos) (hτleavg := hτleavg) (hMeet := hMeet) (hTwoLe := hTwoLe)

end Sieve.Tests
