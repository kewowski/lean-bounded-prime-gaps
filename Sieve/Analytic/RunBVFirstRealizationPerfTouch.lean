/-
  Sieve/Analytic/RunBVFirstRealizationPerfTouch.lean
  UTF-8 (no BOM), ASCII-only.

  Minimal perf touch: reference `AI_first` so interface drift fails fast.
-/
import Mathlib
import Sieve.Analytic.BVFirstRealization

noncomputable section

namespace Sieve
namespace Analytic

/-- Perf touch: just reference `AI_first` at the right type. -/
theorem perf_touch_ai_first (TB : BVToolboxProgressionsSig) : True := by
  let _ai : AvgWindowHitLB := AI_first TB
  exact True.intro

end Analytic
end Sieve
