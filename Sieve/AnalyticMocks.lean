/-
  Sieve/AnalyticMocks.lean
  Mock analytic inputs: take the actual average as the "lower bound".
-/
import Sieve.AnalyticInputs
import Sieve.Stage3Window
import Sieve.Stage3PrimeFacade

set_option linter.unusedVariables false

noncomputable section
open Classical BigOperators

namespace Sieve
namespace AnalyticInputs

/-- A reusable mock: the "lower bound" equals the actual heavy-set average
    of the window hit count. Perfect for demos and tests. -/
def avgAsLower : AvgWindowHitLB :=
{ lower  := fun W τ H HS _hne =>
    Sieve.Stage3.avgOver (Sieve.MTCore.heavySet W τ)
      (Sieve.Stage3.windowSum H (Sieve.Stage3.hitIndicator HS))
, le_avg := fun _ _ _ _ _ => le_of_eq rfl }

end AnalyticInputs
end Sieve
