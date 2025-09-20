/-
  Sieve/OutcomeBuilders.lean
  Build a Stage-2 Outcome from exact moment equalities, for any Pipeline.Config.
-/
import Mathlib
import Sieve.Pipeline
import Sieve.Stage2Glue
import Sieve.Stage2BoundsFromEq
import Sieve.MaynardWeights
import Sieve.MTMoments
import Sieve.ConstWeight
import Sieve.ConstWeightLemmas

noncomputable section
open Classical

namespace Sieve.OutcomeBuilders
open Sieve.Stage2 Sieve.Stage2Weight

/-- Generic: given any `cfg`, equalities for first/second moments yield an `Outcome W`. -/
def outcome_from_equalities
    (cfg : Sieve.Pipeline.Config)
    (W  : Sieve.MaynardWeights.Weight)
    (M  : ℝ) (h1 : Sieve.MTMoments.firstMoment W = (W.support.card : ℝ) * M)
    (M2 : ℝ) (h2 : Sieve.MTMoments.secondMoment W = (W.support.card : ℝ) * M2) :
    Outcome W :=
  outcome_of_bounds cfg W (bounds_of_equalities W M h1 M2 h2)

/-- Convenience for constant weight: uses your `ConstWeightLemmas` equalities. -/
def outcome_const_with_cfg
    (cfg : Sieve.Pipeline.Config)
    (supp : Finset ℤ) (c : ℝ) (hc : 0 ≤ c) :
    Outcome (Sieve.ConstWeight.const supp c hc) :=
  outcome_from_equalities cfg (Sieve.ConstWeight.const supp c hc)
    c
    (by simpa using Sieve.ConstWeight.firstMoment_const supp c hc)
    (c^2)
    (by simpa using Sieve.ConstWeight.secondMoment_const supp c hc)

end Sieve.OutcomeBuilders
