import Mathlib
import Sieve.Analytic.Constants

noncomputable section

namespace Sieve
namespace Analytic

/--
`BVMainAssumptions P` collects the light hypotheses we assume when feeding
`BVParams` into the Stage-3 analytic input. We keep this tiny and proof-free.
-/
structure BVMainAssumptions (P : BVParams) where
  /-- Nonnegativity of error constants used by simple algebraic rewrites. -/
  Cerr1_nonneg : 0 ≤ P.Cerr1
  Cerr2_nonneg : 0 ≤ P.Cerr2
  /-- The usable lower bound we want to pass to Stage-3 wiring later. -/
  lb_ready : P.lowerFormula ≥ P.threshold

end Analytic
end Sieve
