/-
  Sieve/Stage2Glue.lean
  Glue: package Stage 2's Gallagher B together with moment bounds for a given Weight.
-/
import Mathlib
import Sieve.Pipeline
import Sieve.GallagherHook
import Sieve.Stage2
import Sieve.Stage2Weight
import Sieve.MaynardWeights
import Sieve.MTMoments

noncomputable section
open Classical

namespace Sieve.Stage2

/-- Everything Stage 2 needs for a specific `W`: Gallagher `B` (with nonneg)
    and the certified first/second-moment bounds you built for `W`. -/
structure Outcome (W : Sieve.MaynardWeights.Weight) where
  B        : ℝ
  B_nonneg : 0 ≤ B
  -- we carry the numeric caps too, to make the bounds easy to reuse:
  M   : ℝ
  M2  : ℝ
  first_le  : Sieve.MTMoments.firstMoment W ≤ (W.support.card : ℝ) * M
  second_le : Sieve.MTMoments.secondMoment W ≤ (W.support.card : ℝ) * M2

/-- Build an `Outcome W` from a pipeline config and the moment bounds you already have. -/
def outcome_of_bounds
    (cfg : Sieve.Pipeline.Config)
    (W   : Sieve.MaynardWeights.Weight)
    (mb  : Sieve.Stage2Weight.MomentBounds W) : Outcome W :=
{ B        := cfg.contract.gallagher.B
, B_nonneg := cfg.contract.gallagher.nonneg
, M        := mb.M
, M2       := mb.M2
, first_le := mb.first_le
, second_le := mb.second_le }

end Sieve.Stage2
