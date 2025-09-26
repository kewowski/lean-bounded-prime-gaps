/-
  Sieve/Analytic/RunToyAIOnTwinWindow.lean
  Demo: run the Stage-3 twin-window existence theorem on the toy weight `W0`
  (support {0}, w 0 = 1), using either a generic `AI` or the BV "avg-as-lower" AI.
-/
import Mathlib
import Sieve.Analytic.ToyWeightDemo
import Sieve.Stage3TwinGap
import Sieve.Analytic.BVMainStatementWire  -- for AI_of_BV

noncomputable section
open Classical BigOperators

namespace Sieve
namespace Analytic

/-- Generic demo: with any `AI : AvgWindowHitLB`, if `τ ≤ 1` so the heavy set of `W0`
    is nonempty and `(2 : ℝ) ≤ AI.lower …`, then there exists an `n` with at least two
    prime hits in the twin window at `n`. -/
theorem exists_twin_window_from_AI_on_W0
  (AI : Sieve.Analytic.AvgWindowHitLB)
  (cfg : Sieve.MTCore.TupleConfig) {τ : ℝ}
  (hτle : τ ≤ 1)
  (h2 :
    (2 : ℝ) ≤
      AI.lower Sieve.Analytic.W0 τ (([0, 2] : List ℤ).toFinset) (Sieve.Stage3.primeHS cfg)
        (Sieve.Analytic.heavySet_W0_nonempty_of_tau_le_one (τ := τ) hτle)) :
  ∃ n : ℤ,
    2 ≤
      Sieve.Stage3.windowHitCount (([0, 2] : List ℤ).toFinset)
        (Sieve.Stage3.primeHS cfg) n := by
  classical
  -- `0 < |support|` for W0
  have hpos : 0 < Sieve.Analytic.W0.support.card := by
    simpa [Sieve.Analytic.W0_support]  -- 0 < 1
  -- `τ ≤ avg weight` since avg = 1 for W0
  have hτleavg :
      τ ≤ (∑ m ∈ Sieve.Analytic.W0.support, Sieve.Analytic.W0.w m)
            / (Sieve.Analytic.W0.support.card : ℝ) := by
    simpa [Sieve.Analytic.W0_support, Sieve.Analytic.W0_w_zero]
      using hτle
  -- Apply the Stage-3 existence bridge (k = 2 case already provided).
  exact
    Sieve.Stage3TwinGap.exists_twin_window_with_two_primes_of_AI_ge_two_from_avg
      (AI := AI) (W := Sieve.Analytic.W0) (τ := τ) (cfg := cfg)
      (hpos := hpos) (hτleavg := hτleavg) (h2 := h2)

/-- BV "avg-as-lower" demo: with `AI_of_BV`, the lower bound equals the average by def.
    If you assume `(2 : ℝ) ≤ avgOver heavySet (windowSum …)`, you get the same existence. -/
theorem exists_twin_window_from_AI_of_BV_on_W0
  (P : Sieve.Analytic.BVParams) (A : Sieve.Analytic.BVMainAssumptions P)
  (cfg : Sieve.MTCore.TupleConfig) {τ : ℝ}
  (hτle : τ ≤ 1)
  (h2avg :
    (2 : ℝ) ≤
      Sieve.Stage3.avgOver (Sieve.MTCore.heavySet Sieve.Analytic.W0 τ)
        (Sieve.Stage3.windowSum (([0, 2] : List ℤ).toFinset)
          (Sieve.Stage3.hitIndicator (Sieve.Stage3.primeHS cfg)))) :
  ∃ n : ℤ,
    2 ≤
      Sieve.Stage3.windowHitCount (([0, 2] : List ℤ).toFinset)
        (Sieve.Stage3.primeHS cfg) n := by
  classical
  let AI := Sieve.Analytic.AI_of_BV P A
  -- For AI_of_BV, `lower = avg` by construction.
  have h2 :
    (2 : ℝ) ≤
      AI.lower Sieve.Analytic.W0 τ (([0, 2] : List ℤ).toFinset) (Sieve.Stage3.primeHS cfg)
        (Sieve.Analytic.heavySet_W0_nonempty_of_tau_le_one (τ := τ) hτle) := by
    simpa using h2avg
  exact exists_twin_window_from_AI_on_W0 (AI := AI) (cfg := cfg) (τ := τ) hτle h2

end Analytic
end Sieve
