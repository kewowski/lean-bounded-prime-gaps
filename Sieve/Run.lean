/-
  Sieve/Run.lean
  Clean runnable demo: constant weight on a symmetric window, pushed through Stage 1,
  with exact first/second moment equalities (using ConstWeightLemmas).
-/
import Mathlib
import Sieve.AdmissibleTwin
import Sieve.Pipeline
import Sieve.GallagherHook
import Sieve.ConstWeight
import Sieve.ConstWeightLemmas
import Sieve.MTMoments
import Sieve.PipelineSimp

noncomputable section
open Classical

namespace Sieve.Run

/-- Symmetric integer window `[-M, M]` as a `Finset`. -/
def window (M : ℕ) : Finset ℤ :=
  Finset.Icc (-(Int.ofNat M)) (Int.ofNat M)

/-- Constant weight `1` on `window M`. -/
def W (M : ℕ) : Sieve.MaynardWeights.Weight :=
  Sieve.ConstWeight.const (window M) (1 : ℝ) (by norm_num)

/-- Config: conservative Gallagher contract + twin tuple `{0,2}`. -/
def cfg : Sieve.Pipeline.Config :=
{ chars      := Character.decomp_available
, contract   := Sieve.GallagherHook.contract
, tuple      := Sieve.AdmissibleTwin.twin
, admissible := Sieve.AdmissibleTwin.admissible_twin }

/-- Exact first-moment for the constant weight. -/
lemma first_eq (M : ℕ) :
    Sieve.MTMoments.firstMoment (W M) = ((window M).card : ℝ) := by
  simpa [W] using
    (Sieve.ConstWeight.firstMoment_const (window M) (1 : ℝ) (by norm_num))

/-- Exact second-moment for the constant weight. -/
lemma second_eq (M : ℕ) :
    Sieve.MTMoments.secondMoment (W M) = ((window M).card : ℝ) := by
  -- since c = 1, c^2 = 1
  simpa [W, pow_two] using
    (Sieve.ConstWeight.secondMoment_const (window M) (1 : ℝ) (by norm_num))

/-- Stage 1 carries those equalities through to `hits.firstMomentLower`. -/
example (M : ℕ) :
    (Sieve.Pipeline.stage1 cfg (W M)).hits.firstMomentLower
      = ((window M).card : ℝ) := by
  -- `stage1_hits_first` is `rfl`: hits.firstMomentLower = firstMoment (W M)
  have h := Sieve.Pipeline.stage1_hits_first cfg (W M)
  simpa [h] using first_eq M

/-- And to `hits.secondMomentUpper`. -/
example (M : ℕ) :
    (Sieve.Pipeline.stage1 cfg (W M)).hits.secondMomentUpper
      = ((window M).card : ℝ) := by
  have h := Sieve.Pipeline.stage1_hits_second cfg (W M)
  simpa [h] using second_eq M

end Sieve.Run
