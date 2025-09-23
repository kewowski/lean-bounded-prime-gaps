/-
  Sieve/Analytic/PerfHarness.lean
  UTF-8 (no BOM), ASCII-only.

  Minimal perf touch: keep stable surfaces in the build graph without
  depending on brittle aliases (e.g. `dps_flip_tail`). This avoids unsolved
  goals while still catching signature drift via references.
-/
import Mathlib
import Sieve.Analytic.BVToolboxProgressionsSig
import Sieve.Analytic.BVFirstRealization

namespace Sieve.Analytic

section
variable (TB : BVToolboxProgressionsSig)

/-- Touch a stable toolbox field so changes surface in CI. -/
@[noinline] def _perf_touch_C_LS := TB.C_LS

/-- Touch `AI_first` without committing to internals. -/
@[noinline] noncomputable def _perf_touch_AI_first := AI_first TB

/-- Keep module nonempty and lint-clean. -/
theorem _perf_harness_ok : True := trivial

end
end Sieve.Analytic

