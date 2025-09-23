/-
  Sieve/ConditionalTwin.lean
  Conditional twin conclusion via the analytic bridge.
-/
import Sieve.Stage3PrimesEndToEnd

noncomputable section
open Classical BigOperators

namespace Sieve
namespace Conditional

/-- If the analytic lower bound (with prime façade) is ≥ 1 on the heavy set,
and `τ ≤ average`, then there exists a heavy point whose twin window `{0,2}` contains a prime. -/
theorem twin_of_AI_ge_one_from_avg
    (AI : Sieve.Analytic.AvgWindowHitLB)
    (W : Sieve.MaynardWeights.Weight) (τ : ℝ)
    (cfg : Sieve.MTCore.TupleConfig)
    (hpos : 0 < W.support.card)
    (hτleavg :
      τ ≤ (∑ m ∈ W.support, W.w m) / (W.support.card : ℝ))
    (h1 :
      1 ≤ AI.lower W τ (([0, 2] : List ℤ).toFinset) (Sieve.Stage3.primeHS cfg)
            (Sieve.Stage3.heavySet_nonempty_of_avg_ge (W := W) (τ := τ) hpos hτleavg)) :
    ∃ n ∈ Sieve.MTCore.heavySet W τ,
      ∃ h ∈ (([0, 2] : List ℤ).toFinset), Sieve.Stage3.isPrimeZ (n + h) := by
  simpa using
    Sieve.Stage3.exists_prime_in_twin_window_of_AI_ge_one_from_avg
      (AI := AI) (W := W) (τ := τ) (cfg := cfg)
      (hpos := hpos) (hτleavg := hτleavg) (h1 := h1)

end Conditional
end Sieve
