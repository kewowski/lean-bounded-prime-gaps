/-
  Sieve/Analytic/BVMainHelpers.lean
  UTF-8 (no BOM), ASCII-only.

  Tiny algebra-only wrappers that “massage” the BV parameters/assumptions
  into convenient inequality shapes. No heavy analysis; leaf imports only.
-/
import Mathlib
import Sieve.Analytic.Constants
import Sieve.Analytic.BVSketchParams
import Sieve.Analytic.BVMainAssumptions

noncomputable section

namespace Sieve
namespace Analytic

/-- From the assumption bundle, restate the lower-bound direction with `≤`. -/
lemma threshold_le_lower (P : BVParams) (A : BVMainAssumptions P) :
    P.threshold ≤ P.lowerFormula :=
  A.lb_ready

/-- Same as `threshold_le_lower` but phrased via `lowerFormulaParams`. -/
lemma threshold_le_lower_params (P : BVParams) (A : BVMainAssumptions P) :
    P.threshold ≤ lowerFormulaParams P := by
  -- `lowerFormulaParams P = P.lowerFormula` by definition.
  simpa [lowerFormulaParams, BVParams.lowerFormula] using A.lb_ready

/-- If the threshold is nonnegative, then the available lower bound is nonnegative. -/
lemma lower_nonneg_of_threshold_nonneg (P : BVParams) (A : BVMainAssumptions P)
    (hτ : 0 ≤ P.threshold) : 0 ≤ P.lowerFormula :=
  le_trans hτ A.lb_ready

/-- A convenient upper bound using nonnegativity of error constants from `A`. -/
lemma lower_le_Cmain (P : BVParams) (A : BVMainAssumptions P) :
    P.lowerFormula ≤ P.Cmain :=
  BVParams.lowerFormula_le_Cmain P A.Cerr1_nonneg A.Cerr2_nonneg

end Analytic
end Sieve
