/-
  Sieve/Stage2Summary.lean
  Package Stage-1 hit bounds directly from an `Outcome W`.
-/
import Mathlib
import Sieve.Pipeline
import Sieve.Stage2Glue
import Sieve.Stage2Basic
import Sieve.MaynardWeights
import Sieve.MTMoments

noncomputable section
open Classical

namespace Sieve.Stage2

/-- Stage-1 hit bounds + Gallagher `B`, specialized from an `Outcome W`. -/
structure HitOutcome (cfg : Sieve.Pipeline.Config) (W : Sieve.MaynardWeights.Weight) where
  B            : ℝ
  B_nonneg     : 0 ≤ B
  M            : ℝ
  M2           : ℝ
  first_hit_le  :
    (Sieve.Pipeline.stage1 cfg W).hits.firstMomentLower
      ≤ (W.support.card : ℝ) * M
  second_hit_le :
    (Sieve.Pipeline.stage1 cfg W).hits.secondMomentUpper
      ≤ (W.support.card : ℝ) * M2

/-- Build `HitOutcome` from a precomputed `Outcome W`. -/
def hitOutcome_of_outcome
    (cfg : Sieve.Pipeline.Config)
    (W   : Sieve.MaynardWeights.Weight)
    (out : Outcome W) : HitOutcome cfg W :=
{ B            := out.B
, B_nonneg     := out.B_nonneg
, M            := out.M
, M2           := out.M2
, first_hit_le := by simpa using first_le_of_outcome cfg W out
, second_hit_le := by simpa using second_le_of_outcome cfg W out }

end Sieve.Stage2
