import Sieve.Stage2Report
/-
  Sieve/RunStage2ReportSimpleDemo.lean
  Demo: twins + constant weight + simple (non-zero) Gallagher → compact Stage-2 Report.
-/
import Mathlib
import Sieve.ConfigBuilders
import Sieve.AdmissibleTwin
import Sieve.ConstWeight
import Sieve.OutcomeBuilders
import Sieve.Stage2Report

noncomputable section
open Classical

namespace Sieve.RunStage2ReportSimpleDemo

/-- Symmetric integer window `[-M, M]`. -/
def window (M : ℕ) : Finset ℤ :=
  Finset.Icc (-(Int.ofNat M)) (Int.ofNat M)

/-- Compact Stage-2 report using the **simple** Gallagher contract on `[-M,M]`
    with absolute cap `Mabs`, for a constant weight of height `c ≥ 0`. -/
def report (M : ℕ) (Mabs c : ℝ) (hc : 0 ≤ c) :
    Sieve.Stage2Report.Report
      (Sieve.ConfigBuilders.simple (window M) Mabs
         Sieve.AdmissibleTwin.twin Sieve.AdmissibleTwin.admissible_twin)
      (Sieve.ConstWeight.const (window M) c hc) :=
  let cfg := Sieve.ConfigBuilders.simple (window M) Mabs
               Sieve.AdmissibleTwin.twin Sieve.AdmissibleTwin.admissible_twin
  let supp := window M
  let W    := Sieve.ConstWeight.const supp c hc
  let out  := Sieve.OutcomeBuilders.outcome_const_with_cfg cfg supp c hc
  Sieve.Stage2Report.report_of_outcome cfg W out

/-- Sanity: `B ≥ 0`. -/
example (M : ℕ) (Mabs c : ℝ) (hc : 0 ≤ c) :
    0 ≤ (report M Mabs c hc).B :=
  (report M Mabs c hc).B_nonneg

/-- First-moment hit bound under the simple contract. -/
example (M : ℕ) (Mabs c : ℝ) (hc : 0 ≤ c) :
    (Sieve.Pipeline.stage1
        (Sieve.ConfigBuilders.simple (window M) Mabs
          Sieve.AdmissibleTwin.twin Sieve.AdmissibleTwin.admissible_twin)
        (Sieve.ConstWeight.const (window M) c hc)).hits.firstMomentLower
      ≤ ((window M).card : ℝ) * (report M Mabs c hc).M :=
  (report M Mabs c hc).first_hit_le

/-- Squared first-moment bound under the simple contract. -/
example (M : ℕ) (Mabs c : ℝ) (hc : 0 ≤ c) :
    ((Sieve.Pipeline.stage1
        (Sieve.ConfigBuilders.simple (window M) Mabs
          Sieve.AdmissibleTwin.twin Sieve.AdmissibleTwin.admissible_twin)
        (Sieve.ConstWeight.const (window M) c hc)).hits.firstMomentLower)^2
      ≤ ((window M).card : ℝ)^2 * (report M Mabs c hc).M^2 :=
  (report M Mabs c hc).first_hit_sq_le

end Sieve.RunStage2ReportSimpleDemo


