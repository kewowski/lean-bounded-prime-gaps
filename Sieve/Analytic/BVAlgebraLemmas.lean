/-
  Sieve/Analytic/BVAlgebraLemmas.lean
  UTF-8 (no BOM), ASCII-only.

  Purpose
  -------
  Tiny, algebra-only facts about `BVParams.lowerFormula`, kept separate so the
  core constants file stays minimal. These lemmas are fast and proof-light.
-/
import Mathlib
import Sieve.Analytic.Constants
import Sieve.Analytic.BVMainAssumptions

noncomputable section

namespace Sieve
namespace Analytic
namespace BVParams

/-- If both error constants vanish, the lower formula is just `Cmain`. -/
lemma lowerFormula_errors_zero (P : BVParams)
    (h1 : P.Cerr1 = 0) (h2 : P.Cerr2 = 0) :
    P.lowerFormula = P.Cmain := by
  simp [BVParams.lowerFormula, h1, h2]

end BVParams

/-- From the assumption bundle: `threshold ≤ Cmain`. -/
lemma threshold_le_Cmain_of_lb_ready (P : BVParams) (A : BVMainAssumptions P) :
    P.threshold ≤ P.Cmain := by
  -- `threshold ≤ lowerFormula` from `A.lb_ready`, and `lowerFormula ≤ Cmain`
  -- from the algebraic inequality in `BVParams`.
  exact (le_trans A.lb_ready (BVParams.lowerFormula_le_Cmain P A.Cerr1_nonneg A.Cerr2_nonneg))

end Analytic
end Sieve
