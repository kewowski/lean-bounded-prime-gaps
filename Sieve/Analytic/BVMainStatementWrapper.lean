/-
  Sieve/Analytic/BVMainStatementWrapper.lean
  Turn a BV main statement witness into an AvgWindowHitLB (lower = lowerFormulaParams P).
-/
import Mathlib
import Sieve.Analytic.BVMainStatement
import Sieve.Analytic.BVSketchParams
import Sieve.AnalyticInputs
import Sieve.Analytic.AIConstructors

noncomputable section
open Classical

namespace Sieve
namespace Analytic

open AnalyticInputs

/-- Build `AvgWindowHitLB` from a BV main statement `h`.
    The lower function is the constant `lowerFormulaParams P`. -/
def AI_of_BVMainStatement (P : BVParams) (_TB : BVToolbox)
  (h : BVMainStatement P _TB) : AvgWindowHitLB :=
  AnalyticInputs.ofLower
    (fun _W _τ _H _HS _hne => lowerFormulaParams (P := P))
    (fun W τ H HS hne => h W τ H HS hne)

end Analytic
end Sieve
