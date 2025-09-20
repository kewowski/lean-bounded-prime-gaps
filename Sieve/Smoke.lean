/-
  Sieve/Smoke.lean
  UTF-8 (no BOM), ASCII-only.

  A minimal smoke test that constructs stage 1 data and proves
  the zero-weight moments are zero (keeps the pipeline exercised).
-/
import Mathlib
import Sieve.NaiveWeight
import Sieve.MTMoments
import Sieve.Pipeline
import Sieve.Examples

noncomputable section
open Classical

namespace Sieve.Smoke

/-- Stage 1 built package for the trivial pipeline and zero weight. -/
def built : Sieve.MaynardWeights.BuiltWeight :=
  Sieve.Pipeline.stage1 Sieve.Examples.trivialPipeline Sieve.NaiveWeight.zeroWeight

/-- The first moment of the zero weight is zero. -/
lemma firstMoment_zero :
    Sieve.MTMoments.firstMoment Sieve.NaiveWeight.zeroWeight = 0 := by
  classical
  simp [Sieve.MTMoments.firstMoment, Sieve.NaiveWeight.zeroWeight]

/-- The second moment of the zero weight is zero. -/
lemma secondMoment_zero :
    Sieve.MTMoments.secondMoment Sieve.NaiveWeight.zeroWeight = 0 := by
  classical
  simp [Sieve.MTMoments.secondMoment, Sieve.NaiveWeight.zeroWeight]

end Sieve.Smoke
