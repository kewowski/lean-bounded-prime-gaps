import Mathlib
import Sieve.Analytic.RunTwinWindowFromBVMain

noncomputable section
open Classical

namespace Sieve
namespace EndToEnd

/-- Stage-2 facing wrapper: from a BV main-statement witness with `2 ≤ lowerFormulaParams P`,
    produce an `n` whose twin window has at least two prime hits (uses the analytic theorem). -/
theorem twin_window_from_BVMain
  (P : Sieve.Analytic.BVParams) (TB : Sieve.Analytic.BVToolbox)
  (h : Sieve.Analytic.BVMainStatement P TB)
  (cfg : Sieve.MTCore.TupleConfig)
  (W : Sieve.MaynardWeights.Weight) (τ : ℝ)
  (hpos : 0 < W.support.card)
  (hτleavg : τ ≤ (∑ m ∈ W.support, W.w m) / (W.support.card : ℝ))
  (hLower2 : (2 : ℝ) ≤ Sieve.Analytic.lowerFormulaParams (P := P)) :
  ∃ n : ℤ,
    2 ≤
      Sieve.Stage3.windowHitCount (([0, 2] : List ℤ).toFinset)
        (Sieve.Stage3.primeHS cfg) n := by
  simpa using
    Sieve.Analytic.exists_twin_window_from_BVMain
      (P := P) (TB := TB) (h := h) (cfg := cfg) (W := W) (τ := τ)
      (hpos := hpos) (hτleavg := hτleavg) (hLower2 := hLower2)

end EndToEnd
end Sieve
