/-
  Sieve/Analytic/RunTwinWindowFromBVThreshold.lean
  From BV main statement + (2 ≤ threshold ≤ lowerFormulaParams), deduce a twin-window witness.
-/
import Mathlib
import Sieve.Analytic.BVSketchParams
import Sieve.Analytic.BVMainStatement
import Sieve.Analytic.BVMainStatementWrapper
import Sieve.Stage3TwinGap
import Sieve.Analytic.RunTwinWindowFromBVMain


noncomputable section
open Classical

namespace Sieve
namespace Analytic

/-- If BV main statement holds for `P`, and `P` meets its threshold with `2 ≤ P.threshold`,
    then there exists `n` whose twin window has at least two prime hits (under the standard
    heavy-set nonemptiness hypothesis). -/
theorem exists_twin_window_from_BVMain_threshold
  (P : BVParams) (TB : BVToolbox)
  (h : BVMainStatement P TB)
  (cfg : Sieve.MTCore.TupleConfig)
  (W : Sieve.MaynardWeights.Weight) (τ : ℝ)
  (hpos : 0 < W.support.card)
  (hτleavg : τ ≤ (∑ m ∈ W.support, W.w m) / (W.support.card : ℝ))
  (hMeet : meetsThreshold P)                -- lowerFormulaParams P ≥ P.threshold
  (hTwoLe : (2 : ℝ) ≤ P.threshold) :
  ∃ n : ℤ,
    2 ≤
      Sieve.Stage3.windowHitCount (([0, 2] : List ℤ).toFinset)
        (Sieve.Stage3.primeHS cfg) n := by
  classical
  -- Derive `2 ≤ lowerFormulaParams P` from the two inequalities.
  have hLower2 : (2 : ℝ) ≤ lowerFormulaParams (P := P) := by
    have : P.threshold ≤ lowerFormulaParams (P := P) := by
      simpa [meetsThreshold_def] using hMeet
    exact le_trans hTwoLe this
  -- Apply the BV main-statement wrapper (AI_of_BVMainStatement) route:
  exact
    Sieve.Analytic.exists_twin_window_from_BVMain
      (P := P) (TB := TB) (h := h) (cfg := cfg)
      (W := W) (τ := τ) (hpos := hpos) (hτleavg := hτleavg) (hLower2 := hLower2)

end Analytic
end Sieve
