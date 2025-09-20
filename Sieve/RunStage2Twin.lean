/-
  Sieve/RunStage2Twin.lean
  Demo: build Stage 2 outcome for any Weight using twinConfig + pointwise caps.
-/
import Mathlib
import Sieve.AdmissibleTwin
import Sieve.Stage2Glue
import Sieve.Stage2Weight
import Sieve.MaynardWeights
import Sieve.MTMoments

noncomputable section
open Classical

namespace Sieve.RunStage2Twin

open Sieve.Stage2Weight
open Sieve.Stage2

/-- Given any weight `W` and simple pointwise caps on its support,
    package the Stage-2 outcome for the twin tuple `{0,2}`. -/
def outcomeFor
    (W   : Sieve.MaynardWeights.Weight)
    (M   : ℝ) (hub  : ∀ n ∈ W.support, W.w n ≤ M)
    (M2  : ℝ) (hub2 : ∀ n ∈ W.support, (W.w n)^2 ≤ M2) :
    Outcome W :=
  outcome_of_bounds Sieve.AdmissibleTwin.twinConfig W
    (bounds_of_pointwise W M hub M2 hub2)

/-- The Gallagher `B` is nonnegative in this twin setup (conservative contract). -/
example (W : Sieve.MaynardWeights.Weight)
        (M : ℝ) (hub : ∀ n ∈ W.support, W.w n ≤ M)
        (M2 : ℝ) (hub2 : ∀ n ∈ W.support, (W.w n)^2 ≤ M2) :
        0 ≤ (outcomeFor W M hub M2 hub2).B :=
  (outcomeFor W M hub M2 hub2).B_nonneg

/-- First-moment bound follows directly from the packaged outcome. -/
example (W : Sieve.MaynardWeights.Weight)
        (M : ℝ) (hub : ∀ n ∈ W.support, W.w n ≤ M)
        (M2 : ℝ) (hub2 : ∀ n ∈ W.support, (W.w n)^2 ≤ M2) :
        Sieve.MTMoments.firstMoment W
          ≤ (W.support.card : ℝ) * (outcomeFor W M hub M2 hub2).M :=
  (outcomeFor W M hub M2 hub2).first_le

/-- Second-moment bound ditto. -/
example (W : Sieve.MaynardWeights.Weight)
        (M : ℝ) (hub : ∀ n ∈ W.support, W.w n ≤ M)
        (M2 : ℝ) (hub2 : ∀ n ∈ W.support, (W.w n)^2 ≤ M2) :
        Sieve.MTMoments.secondMoment W
          ≤ (W.support.card : ℝ) * (outcomeFor W M hub M2 hub2).M2 :=
  (outcomeFor W M hub M2 hub2).second_le

end Sieve.RunStage2Twin
