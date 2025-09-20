/-
  Sieve/ConstTwinOutcome.lean
  Package a Stage-2 Outcome for the twin config using a constant weight.
  Now includes a convenience `outcomeConst` that uses the exact lemmas.
-/
import Mathlib
import Sieve.AdmissibleTwin
import Sieve.MaynardWeights
import Sieve.MTMoments
import Sieve.Stage2BoundsFromEq
import Sieve.Stage2Glue
import Sieve.ConstWeight
import Sieve.ConstWeightLemmas

noncomputable section
open Classical

namespace Sieve.ConstTwinOutcome
open Sieve.Stage2Weight Sieve.Stage2

/-- The constant weight (fully qualified to avoid namespace guesses). -/
def Wconst (supp : Finset ℤ) (c : ℝ) (hc : 0 ≤ c) : Sieve.MaynardWeights.Weight :=
  Sieve.ConstWeight.const supp c hc

/-- Build the Stage-2 outcome for `{0,2}` from *equalities* for a constant weight. -/
def outcomeConst_from_eq
    (supp : Finset ℤ) (c : ℝ) (hc : 0 ≤ c)
    (h1 : Sieve.MTMoments.firstMoment (Wconst supp c hc) = (supp.card : ℝ) * c)
    (h2 : Sieve.MTMoments.secondMoment (Wconst supp c hc) = (supp.card : ℝ) * c^2) :
    Sieve.Stage2.Outcome (Wconst supp c hc) :=
  outcome_of_bounds Sieve.AdmissibleTwin.twinConfig (Wconst supp c hc)
    (bounds_of_equalities (Wconst supp c hc) c h1 (c^2) h2)

/-- Convenience: use the exact lemmas from `Sieve.ConstWeightLemmas`. -/
def outcomeConst (supp : Finset ℤ) (c : ℝ) (hc : 0 ≤ c) :
    Sieve.Stage2.Outcome (Wconst supp c hc) :=
  outcomeConst_from_eq supp c hc
    (by simpa using Sieve.ConstWeight.firstMoment_const supp c hc)
    (by simpa using Sieve.ConstWeight.secondMoment_const supp c hc)

/-- Tiny sanity: Gallagher B is nonneg for the twin setup with constant weight. -/
example (supp : Finset ℤ) (c : ℝ) (hc : 0 ≤ c) :
    0 ≤ (outcomeConst supp c hc).B :=
  (outcomeConst supp c hc).B_nonneg

end Sieve.ConstTwinOutcome
