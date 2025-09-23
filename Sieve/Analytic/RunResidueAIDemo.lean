/-
  Sieve/Analytic/RunResidueAIDemo.lean
  UTF-8 (no BOM), ASCII-only.

  Tiny demo: touch the residue→AI adapter by threading `AI_first` through it.
  Purpose: keep the residue path in the build graph without heavy deps.
-/
import Sieve.Analytic.ResidueAI
import Sieve.Analytic.BVFirstRealization

namespace Sieve.Analytic

/-- Touch `AI_from_residuePointwise (AI_first TB)` to catch signature drift. -/
theorem _residue_ai_touch (TB : BVToolboxProgressionsSig) : True := by
  let _ai : AvgWindowHitLB := AI_from_residuePointwise (AI_first TB)
  exact trivial

end Sieve.Analytic
