/-
  Sieve/RunStage2ReportCompare.lean
  Side-by-side Stage-2 reports: conservative vs simple Gallagher on twins + const weight.
-/
import Mathlib
import Sieve.ConfigBuilders
import Sieve.AdmissibleTwin
import Sieve.ConstWeight
import Sieve.OutcomeBuilders
import Sieve.Stage2Report

noncomputable section
open Classical

namespace Sieve.RunStage2ReportCompare

/-- Symmetric integer window `[-M, M]`. -/
def window (M : ℕ) : Finset ℤ :=
  Finset.Icc (-(Int.ofNat M)) (Int.ofNat M)

/-- Compact Stage-2 report under the **conservative** contract. -/
def reportConservative (M : ℕ) (c : ℝ) (hc : 0 ≤ c) :
    Sieve.Stage2.Report
      (Sieve.ConfigBuilders.conservative
         Sieve.AdmissibleTwin.twin Sieve.AdmissibleTwin.admissible_twin)
      (Sieve.ConstWeight.const (window M) c hc) :=
  let cfg  := Sieve.ConfigBuilders.conservative
                Sieve.AdmissibleTwin.twin Sieve.AdmissibleTwin.admissible_twin
  let supp := window M
  let W    := Sieve.ConstWeight.const supp c hc
  let out  := Sieve.OutcomeBuilders.outcome_const_with_cfg cfg supp c hc
  Sieve.Stage2.report_of_outcome cfg W out

/-- Compact Stage-2 report under the **simple** (non-zero) Gallagher contract on `[-M,M]`
    with absolute cap `Mabs`. -/
def reportSimple (M : ℕ) (Mabs c : ℝ) (hc : 0 ≤ c) :
    Sieve.Stage2.Report
      (Sieve.ConfigBuilders.simple (window M) Mabs
         Sieve.AdmissibleTwin.twin Sieve.AdmissibleTwin.admissible_twin)
      (Sieve.ConstWeight.const (window M) c hc) :=
  let cfg  := Sieve.ConfigBuilders.simple (window M) Mabs
                Sieve.AdmissibleTwin.twin Sieve.AdmissibleTwin.admissible_twin
  let supp := window M
  let W    := Sieve.ConstWeight.const supp c hc
  let out  := Sieve.OutcomeBuilders.outcome_const_with_cfg cfg supp c hc
  Sieve.Stage2.report_of_outcome cfg W out

/-- Sanity: `B ≥ 0` in the conservative report. -/
example (M : ℕ) (c : ℝ) (hc : 0 ≤ c) :
    0 ≤ (reportConservative M c hc).B :=
  (reportConservative M c hc).B_nonneg

/-- Sanity: `B ≥ 0` in the simple report. -/
example (M : ℕ) (Mabs c : ℝ) (hc : 0 ≤ c) :
    0 ≤ (reportSimple M Mabs c hc).B :=
  (reportSimple M Mabs c hc).B_nonneg

/-- In the **conservative** case, `B = 0` by definition. -/
example (M : ℕ) (c : ℝ) (hc : 0 ≤ c) :
    (reportConservative M c hc).B = 0 := rfl

/-- In the **simple** case, `B = (card [-M,M])^2 · Mabs^2` by definition. -/
example (M : ℕ) (Mabs c : ℝ) (hc : 0 ≤ c) :
    (reportSimple M Mabs c hc).B = ((window M).card : ℝ)^2 * Mabs^2 := rfl

end Sieve.RunStage2ReportCompare
