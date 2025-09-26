/-
  Sieve/Analytic/RunTwinWindowFromBVMain.lean
  Use a BV main-statement witness to produce a twin-window witness with ≥ 2 prime hits.
-/
import Mathlib
import Sieve.Analytic.BVMainStatement
import Sieve.Analytic.BVMainStatementWrapper
import Sieve.Stage3TwinGap

noncomputable section
open Classical

namespace Sieve
namespace Analytic

/-- If the BV main statement holds for `P` (with any toolbox), and
    `2 ≤ lowerFormulaParams P`, then for any `W, τ` with a nonempty heavy set
    (witnessed via `τ ≤ avg`), there exists `n` whose twin window has at least
    two prime hits. -/
theorem exists_twin_window_from_BVMain
  (P : BVParams) (TB : BVToolbox)
  (h : BVMainStatement P TB)
  (cfg : Sieve.MTCore.TupleConfig)
  (W : Sieve.MaynardWeights.Weight) (τ : ℝ)
  (hpos : 0 < W.support.card)
  (hτleavg : τ ≤ (∑ m ∈ W.support, W.w m) / (W.support.card : ℝ))
  (hLower2 : (2 : ℝ) ≤ lowerFormulaParams (P := P)) :
  ∃ n : ℤ,
    2 ≤
      Sieve.Stage3.windowHitCount (([0, 2] : List ℤ).toFinset)
        (Sieve.Stage3.primeHS cfg) n := by
  classical
  -- Build the analytic interface with lower = lowerFormulaParams P.
  let AI := AI_of_BVMainStatement (P := P) (_TB := TB) h
  -- Since AI.lower = lowerFormulaParams P by definition, this is immediate.
  have h2 :
      (2 : ℝ) ≤
        AI.lower W τ (([0, 2] : List ℤ).toFinset) (Sieve.Stage3.primeHS cfg)
          (Sieve.Stage3.heavySet_nonempty_of_avg_ge (W := W) (τ := τ) hpos hτleavg) := by
    simpa using hLower2
  -- Apply the Stage-3 twin-window existence result.
  exact
    Sieve.Stage3TwinGap.exists_twin_window_with_two_primes_of_AI_ge_two_from_avg
      (AI := AI) (W := W) (τ := τ) (cfg := cfg)
      (hpos := hpos) (hτleavg := hτleavg) (h2 := h2)

end Analytic
end Sieve
