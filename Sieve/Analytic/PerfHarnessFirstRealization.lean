/-
  Sieve/Analytic/PerfHarnessFirstRealization.lean
  UTF-8 (no BOM), ASCII-only.

  Purpose: keep the new surfaces “hot” so CI trips on any signature drift.
-/
import Mathlib
import Sieve.Analytic.BVFirstRealization
import Sieve.Analytic.BVFirstRealizationTB
import Sieve.Analytic.BVFirstPiecesChain

noncomputable section

namespace Sieve
namespace Analytic

/-- Touch the simple AI. -/
theorem perf_touch_AI_first (TB : BVToolboxProgressionsSig) : True := by
  let _ai : AvgWindowHitLB := AI_first TB
  exact True.intro

/-- Touch the toolbox-threaded AI. -/
theorem perf_touch_AI_first_TB (TB : BVToolboxProgressionsSig) : True := by
  let _ai : AvgWindowHitLB := AI_first_TB TB
  exact True.intro

/-- Touch the DPS → orthogonality → LS pieces chain. -/
theorem perf_touch_first_chain (TB : BVToolboxProgressionsSig) : True :=
  first_chain_wired TB

end Analytic
end Sieve
