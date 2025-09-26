import Sieve.Stage2Report
/-
  Sieve/RunStage2ReportDemo.lean
  Demo: twins + constant weight → Outcome → compact Stage-2 Report.
-/
import Mathlib
import Sieve.AdmissibleTwin
import Sieve.ConstWeight
import Sieve.OutcomeBuilders
import Sieve.Stage2Report

noncomputable section
open Classical

namespace Sieve.RunStage2ReportDemo

def window (M : ℕ) : Finset ℤ :=
  Finset.Icc (-(Int.ofNat M)) (Int.ofNat M)

/-- Build the compact Stage-2 report for twins + constant weight. -/
def report (M : ℕ) (c : ℝ) (hc : 0 ≤ c) :
    Sieve.Stage2Report.Report Sieve.AdmissibleTwin.twinConfig
      (Sieve.ConstWeight.const (window M) c hc) :=
  let supp := window M
  let W    := Sieve.ConstWeight.const supp c hc
  let out  := Sieve.OutcomeBuilders.outcome_const_with_cfg
                Sieve.AdmissibleTwin.twinConfig supp c hc
  Sieve.Stage2Report.report_of_outcome Sieve.AdmissibleTwin.twinConfig W out

/-- Sanity checks. -/
example (M : ℕ) (c : ℝ) (hc : 0 ≤ c) : 0 ≤ (report M c hc).B :=
  (report M c hc).B_nonneg

example (M : ℕ) (c : ℝ) (hc : 0 ≤ c) :
    (Sieve.Pipeline.stage1 Sieve.AdmissibleTwin.twinConfig
        (Sieve.ConstWeight.const (window M) c hc)).hits.firstMomentLower
      ≤ ((window M).card : ℝ) * (report M c hc).M :=
  (report M c hc).first_hit_le

example (M : ℕ) (c : ℝ) (hc : 0 ≤ c) :
    ((Sieve.Pipeline.stage1 Sieve.AdmissibleTwin.twinConfig
        (Sieve.ConstWeight.const (window M) c hc)).hits.firstMomentLower)^2
      ≤ ((window M).card : ℝ)^2 * (report M c hc).M^2 :=
  (report M c hc).first_hit_sq_le

end Sieve.RunStage2ReportDemo


