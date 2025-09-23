import Mathlib
import Sieve.Analytic.Constants

noncomputable section

namespace Sieve
namespace Analytic

/-
  Sieve/Analytic/BVSketchParams.lean
  UTF-8 (no BOM), ASCII-only.

  Tiny, safe wrappers that expose the lower-bound expression and the
  “meets threshold” predicate we intend to feed into Stage-3.
  No heavy proofs; purely definitional.
-/

/-- The concrete lower-bound expression we will carry through the bridge. -/
def lowerFormulaParams (P : BVParams) : ℝ :=
  BVParams.lowerFormula P

/-- Predicate saying the available lower bound meets the target threshold. -/
def meetsThreshold (P : BVParams) : Prop :=
  lowerFormulaParams P ≥ P.threshold

@[simp] lemma lowerFormulaParams_def (P : BVParams) :
    lowerFormulaParams P = BVParams.lowerFormula P := rfl

@[simp] lemma meetsThreshold_def (P : BVParams) :
    meetsThreshold P = (lowerFormulaParams P ≥ P.threshold) := rfl

end Analytic
end Sieve
