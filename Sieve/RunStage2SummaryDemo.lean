/-
  Sieve/RunStage2SummaryDemo.lean
  Demo: twins + constant weight → Outcome → HitOutcome (Stage 2 bounds).
-/
import Mathlib
import Sieve.AdmissibleTwin
import Sieve.OutcomeBuilders
import Sieve.Stage2Summary
import Sieve.ConstWeight

noncomputable section
open Classical

namespace Sieve.RunStage2SummaryDemo

/-- Symmetric integer window `[-M, M]`. -/
def window (M : ℕ) : Finset ℤ :=
  Finset.Icc (-(Int.ofNat M)) (Int.ofNat M)

/-- Build the Stage-2 `HitOutcome` for twins with a constant weight on `[-M,M]`. -/
def hit (M : ℕ) (c : ℝ) (hc : 0 ≤ c) :
    Sieve.Stage2.HitOutcome Sieve.AdmissibleTwin.twinConfig
      (Sieve.ConstWeight.const (window M) c hc) :=
  let supp := window M
  let W := Sieve.ConstWeight.const supp c hc
  -- Outcome from *equalities* (ConstWeightLemmas) under any config (here: twinConfig).
  let out := Sieve.OutcomeBuilders.outcome_const_with_cfg
               Sieve.AdmissibleTwin.twinConfig supp c hc
  -- Package first/second hit bounds + B into HitOutcome:
  Sieve.Stage2.hitOutcome_of_outcome Sieve.AdmissibleTwin.twinConfig W out

/-- Sanity checks for any `M, c ≥ 0`. -/
example (M : ℕ) (c : ℝ) (hc : 0 ≤ c) :
    0 ≤ (hit M c hc).B :=
  (hit M c hc).B_nonneg

example (M : ℕ) (c : ℝ) (hc : 0 ≤ c) :
    (Sieve.Pipeline.stage1 Sieve.AdmissibleTwin.twinConfig
        (Sieve.ConstWeight.const (window M) c hc)).hits.firstMomentLower
      ≤ ((window M).card : ℝ) * (hit M c hc).M :=
  (hit M c hc).first_hit_le

example (M : ℕ) (c : ℝ) (hc : 0 ≤ c) :
    (Sieve.Pipeline.stage1 Sieve.AdmissibleTwin.twinConfig
        (Sieve.ConstWeight.const (window M) c hc)).hits.secondMomentUpper
      ≤ ((window M).card : ℝ) * (hit M c hc).M2 :=
  (hit M c hc).second_hit_le

end Sieve.RunStage2SummaryDemo
