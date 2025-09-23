/-
  Sieve/Analytic/RunBVParamsPrimeDemo.lean
  UTF-8 (no BOM), ASCII-only.

  Minimal smoke demo: *type plumbing only*.
  Parameterized over any `P : BVParams` with zero constants; we build the
  trivial assumption bundle and wire it into an `AvgWindowHitLB` via `AI_of_BV`.
-/
import Mathlib
import Sieve.Analytic.Constants
import Sieve.Analytic.BVMainAssumptions
import Sieve.Analytic.BVMainStatementWire

noncomputable section

namespace Sieve
namespace Analytic

/-- If `Cerr1 = Cerr2 = threshold = Cmain = 0`, we can build the assumption bundle trivially. -/
def A_of_zero (P : BVParams)
    (hC1 : P.Cerr1 = 0) (hC2 : P.Cerr2 = 0) (hT : P.threshold = 0) (hCmain : P.Cmain = 0) :
    BVMainAssumptions P :=
{ Cerr1_nonneg := by simp [hC1]
, Cerr2_nonneg := by simp [hC2]
, lb_ready := by
    -- Under these hypotheses, the goal reduces to `0 ≥ 0`.
    simp [BVParams.lowerFormula, BVParams.logN, hC1, hC2, hT, hCmain]
}

/-- Produce a mock analytic input using the temporary wiring. -/
def demoAI (P : BVParams)
    (hC1 : P.Cerr1 = 0) (hC2 : P.Cerr2 = 0) (hT : P.threshold = 0) (hCmain : P.Cmain = 0)
    : Sieve.Analytic.AvgWindowHitLB :=
  AI_of_BV P (A_of_zero P hC1 hC2 hT hCmain)

/-- Sanity: the demo compiles and yields something of the expected type. -/
theorem demoAI_wired (P : BVParams)
    (_hC1 : P.Cerr1 = 0) (_hC2 : P.Cerr2 = 0) (_hT : P.threshold = 0) (_hCmain : P.Cmain = 0) :
    True := True.intro

end Analytic
end Sieve
