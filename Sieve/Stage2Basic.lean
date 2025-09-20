/-
  Sieve/Stage2Basic.lean
  Mechanical Stage-2 bounds on stage1 hits from an `Outcome W`.
-/
import Mathlib
import Sieve.Pipeline
import Sieve.PipelineSimp
import Sieve.Stage2Glue
import Sieve.MaynardWeights
import Sieve.MTMoments

noncomputable section
open Classical

namespace Sieve.Stage2

/-- From an `Outcome W`, get the first-moment bound on `stage1` hits. -/
lemma first_le_of_outcome
    (cfg : Sieve.Pipeline.Config)
    (W   : Sieve.MaynardWeights.Weight)
    (out : Outcome W) :
    (Sieve.Pipeline.stage1 cfg W).hits.firstMomentLower
      ≤ (W.support.card : ℝ) * out.M := by
  -- `stage1_hits_first` is `rfl`, so this is just `out.first_le`
  simpa using out.first_le

/-- From an `Outcome W`, get the second-moment bound on `stage1` hits. -/
lemma second_le_of_outcome
    (cfg : Sieve.Pipeline.Config)
    (W   : Sieve.MaynardWeights.Weight)
    (out : Outcome W) :
    (Sieve.Pipeline.stage1 cfg W).hits.secondMomentUpper
      ≤ (W.support.card : ℝ) * out.M2 := by
  -- `stage1_hits_second` is `rfl`, so this is just `out.second_le`
  simpa using out.second_le

/-- The Gallagher `B` packaged in the outcome is nonnegative. -/
lemma B_nonneg_of_outcome
    (W   : Sieve.MaynardWeights.Weight)
    (out : Outcome W) :
    0 ≤ out.B :=
  out.B_nonneg

end Sieve.Stage2
