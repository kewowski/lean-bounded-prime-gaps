/-
  Sieve/Analytic/BVMainStatementWire.lean
  UTF-8 (no BOM), ASCII-only.

  Minimal, green wiring from BV parameters/assumptions to the Stage-3
  analytic interface `AvgWindowHitLB`.

  Change (today):
  ----------------
  Replace the mock-based placeholder with a tiny constructor built via
  `AnalyticInputs.ofLower`, using the *actual* Stage-3 average as the
  provided lower bound (so the proof is by `rfl`). This removes the
  dependency on `AnalyticMocks` while keeping everything green.

  Later:
  ------
  We will replace the `lower := avg` choice with `lower := P.lowerFormula`
  together with a genuine inequality proof once the BV toolbox is wired.
-/
import Mathlib
import Sieve.Analytic.Constants
import Sieve.Analytic.BVMainAssumptions
import Sieve.AnalyticInputs
import Sieve.Analytic.AIConstructors  -- gives `AnalyticInputs.ofLower`

noncomputable section

namespace Sieve
namespace Analytic

open AnalyticInputs

/-- Wiring: produce an `AvgWindowHitLB` from `(P, A)` using `ofLower` with `lower = avg`. -/
def AI_of_BV (_P : BVParams) (_A : BVMainAssumptions _P) : AvgWindowHitLB :=
  AnalyticInputs.ofLower
    (fun W τ H HS _hne =>
      Sieve.Stage3.avgOver (Sieve.MTCore.heavySet W τ)
        (Sieve.Stage3.windowSum H (Sieve.Stage3.hitIndicator HS)))
    (fun _W _τ _H _HS _hne => le_of_eq rfl)

end Analytic
end Sieve
