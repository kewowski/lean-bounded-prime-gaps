/-
  Sieve/RunStage2SummarySimpleDemo.lean
  Demo: twins + constant weight + simple (non-zero) Gallagher contract → HitOutcome.
-/
import Mathlib
import Sieve.AdmissibleTwin
import Sieve.GallagherSimple
import Sieve.OutcomeBuilders
import Sieve.Stage2Summary
import Sieve.ConstWeight

noncomputable section
open Classical

namespace Sieve.RunStage2SummarySimpleDemo

/-- Symmetric integer window `[-M, M]`. -/
def window (M : ℕ) : Finset ℤ :=
  Finset.Icc (-(Int.ofNat M)) (Int.ofNat M)

/-- Twin config using the simple non-zero Gallagher contract on `S = [-M,M]`
    with an absolute cap `Mabs` for the Gallagher window terms. -/
def cfg_simple (M : ℕ) (Mabs : ℝ) : Sieve.Pipeline.Config :=
{ chars      := Character.decomp_available
, contract   := Sieve.GallagherSimple.contract_of_absWindow (window M) Mabs
, tuple      := Sieve.AdmissibleTwin.twin
, admissible := Sieve.AdmissibleTwin.admissible_twin }

/-- Package a Stage-2 `HitOutcome` for twins, simple Gallagher, and a constant weight. -/
def hit (M : ℕ) (Mabs c : ℝ) (hc : 0 ≤ c) :
    Sieve.Stage2.HitOutcome (cfg_simple M Mabs)
      (Sieve.ConstWeight.const (window M) c hc) :=
  let supp := window M
  let W := Sieve.ConstWeight.const supp c hc
  -- Outcome from exact equalities for constant weight under the simple config:
  let out := Sieve.OutcomeBuilders.outcome_const_with_cfg
               (cfg_simple M Mabs) supp c hc
  -- Package hit bounds + B:
  Sieve.Stage2.hitOutcome_of_outcome (cfg_simple M Mabs) W out

/-- Sanity: B is nonnegative. -/
example (M : ℕ) (Mabs c : ℝ) (hc : 0 ≤ c) :
    0 ≤ (hit M Mabs c hc).B :=
  (hit M Mabs c hc).B_nonneg

/-- Inspect the simple Gallagher `B`: it is `(card S)^2 * Mabs^2` by definition. -/
example (M : ℕ) (Mabs c : ℝ) (hc : 0 ≤ c) :
    (hit M Mabs c hc).B = ((window M).card : ℝ)^2 * Mabs^2 := rfl

/-- First-moment hit bound under the simple contract. -/
example (M : ℕ) (Mabs c : ℝ) (hc : 0 ≤ c) :
    (Sieve.Pipeline.stage1 (cfg_simple M Mabs)
        (Sieve.ConstWeight.const (window M) c hc)).hits.firstMomentLower
      ≤ ((window M).card : ℝ) * (hit M Mabs c hc).M :=
  (hit M Mabs c hc).first_hit_le

/-- Second-moment hit bound under the simple contract. -/
example (M : ℕ) (Mabs c : ℝ) (hc : 0 ≤ c) :
    (Sieve.Pipeline.stage1 (cfg_simple M Mabs)
        (Sieve.ConstWeight.const (window M) c hc)).hits.secondMomentUpper
      ≤ ((window M).card : ℝ) * (hit M Mabs c hc).M2 :=
  (hit M Mabs c hc).second_hit_le

end Sieve.RunStage2SummarySimpleDemo
