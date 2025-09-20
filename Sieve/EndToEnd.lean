/-
  Sieve/EndToEnd.lean
  Small API: build ready-to-use Stage-2 Reports for twins + constant weights.
-/
import Mathlib
import Sieve.AdmissibleTwin
import Sieve.ConfigBuilders
import Sieve.ConstWeight
import Sieve.OutcomeBuilders
import Sieve.Stage2Report

noncomputable section
open Classical

namespace Sieve.EndToEnd

/-- Symmetric integer window `[-M, M]` (cast-friendly). -/
def window (M : ℕ) : Finset ℤ :=
  Finset.Icc (-(M : ℤ)) (M : ℤ)

/-- End-to-end Stage-2 report for **twins + constant weight** with the conservative contract. -/
def report_twin_const_conservative (M : ℕ) (c : ℝ) (hc : 0 ≤ c) :
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

/-- End-to-end Stage-2 report for **twins + constant weight** with the simple (non-zero) contract. -/
def report_twin_const_simple (M : ℕ) (Mabs c : ℝ) (hc : 0 ≤ c) :
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

/-- Sanity: `B = 0` in the conservative case. -/
example (M : ℕ) (c : ℝ) (hc : 0 ≤ c) :
    (report_twin_const_conservative M c hc).B = 0 := rfl

/-- Sanity: `B = (card [-M,M])^2 · Mabs^2` in the simple case. -/
example (M : ℕ) (Mabs c : ℝ) (hc : 0 ≤ c) :
    (report_twin_const_simple M Mabs c hc).B = ((window M).card : ℝ)^2 * Mabs^2 := rfl

end Sieve.EndToEnd
