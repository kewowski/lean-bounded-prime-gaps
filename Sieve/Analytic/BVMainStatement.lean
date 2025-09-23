/-
  Sieve/Analytic/BVMainStatement.lean
  UTF-8 (no BOM), ASCII-only.

  A single statement to target: given `BVParams` and a toolbox, this is the
  precise inequality that feeds Stage-3. Also provides a helper to build
  `AvgWindowHitLB` from any proof of that statement.
-/
import Mathlib
import Sieve.Analytic.BVSketchParams

noncomputable section
open Classical

namespace Sieve
namespace Analytic

/-- The BV/EH main lower-bound statement we aim to prove (or assume): for the
chosen parameters/toolbox, the parametric lower formula is bounded by the
Stage-3 average window-hit functional. -/
def BVMainStatement
    (P : BVParams) (TB : BVToolbox) : Prop :=
  ∀ (W : Sieve.MaynardWeights.Weight) (τ : ℝ)
    (H : Finset ℤ) (HS : Sieve.Stage3.HitSystem)
    (hne : (Sieve.MTCore.heavySet W τ).Nonempty),
    lowerFormulaParams P W τ H HS hne
      ≤ Sieve.Stage3.avgOver (Sieve.MTCore.heavySet W τ)
          (Sieve.Stage3.windowSum H (Sieve.Stage3.hitIndicator HS))

/-- Turn any proof of `BVMainStatement P TB` into a ready-to-use analytic
provider for Stage-3 wrappers. -/
def AI_of_BV (P : BVParams) (TB : BVToolbox)
    (h : BVMainStatement P TB) : AvgWindowHitLB :=
  bvSketchParams P TB (proof := h)

end Analytic
end Sieve
