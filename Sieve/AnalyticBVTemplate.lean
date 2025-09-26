/-
  Sieve/AnalyticBVTemplate.lean
  Tiny adapter: from a proof of `BVMainStatement` to an `AvgWindowHitLB`.
-/
import Mathlib
import Sieve.Analytic.BVMainStatement
import Sieve.Analytic.BVSketchParams
import Sieve.AnalyticBridge
import Sieve.MTCore
import Sieve.Stage3Window
import Sieve.Stage3PrimeFacade

noncomputable section
open Classical BigOperators

namespace Sieve
namespace Analytic

/-- Package a proof of `BVMainStatement` into the Stage-3 bridge type. -/
def bvSketchParams (P : BVParams) (TB : BVToolbox)
    (proof : BVMainStatement P TB) : AvgWindowHitLB :=
{ lower  := fun _W _τ _H _HS _hne => lowerFormulaParams P
, le_avg := fun W τ H HS hne => proof W τ H HS hne }

/-- Convenience alias. -/
abbrev AI_of_BV (P : BVParams) (TB : BVToolbox)
    (h : BVMainStatement P TB) : AvgWindowHitLB :=
  bvSketchParams P TB (proof := h)

end Analytic
end Sieve
