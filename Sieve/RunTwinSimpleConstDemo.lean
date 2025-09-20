/-
  Sieve/RunTwinSimpleConstDemo.lean
  Demo: twin tuple with simple (non-zero) Gallagher contract and a constant weight.
-/
import Mathlib
import Sieve.AdmissibleTwin
import Sieve.GallagherSimple
import Sieve.Pipeline
import Sieve.OutcomeBuilders
import Sieve.ConstWeight

noncomputable section
open Classical

namespace Sieve.RunTwinSimpleConstDemo
open Sieve.OutcomeBuilders

/-- Twin config using the simple abs-window Gallagher contract. -/
def twinConfig_simple (S : Finset ℤ) (Mabs : ℝ) : Sieve.Pipeline.Config :=
{ chars      := Character.decomp_available
, contract   := Sieve.GallagherSimple.contract_of_absWindow S Mabs
, tuple      := Sieve.AdmissibleTwin.twin
, admissible := Sieve.AdmissibleTwin.admissible_twin }

/-- Package an outcome for twins with:
    - `S`   : the Gallagher window (for B := (|S|)^2 · Mabs^2)
    - `Mabs`: abs cap for the window summands
    - `supp`: support of the constant weight
    - `c≥0` : constant weight value (nonnegative)
Uses exact moment equalities from ConstWeightLemmas. -/
def outcomeTwin_simple_const
    (S supp : Finset ℤ) (Mabs c : ℝ) (hc : 0 ≤ c) :
    Sieve.Stage2.Outcome (Sieve.ConstWeight.const supp c hc) :=
  outcome_const_with_cfg (twinConfig_simple S Mabs) supp c hc

/-- Sanity: B is nonnegative for this setup. -/
example (S supp : Finset ℤ) (Mabs c : ℝ) (hc : 0 ≤ c) :
    0 ≤ (outcomeTwin_simple_const S supp Mabs c hc).B :=
  (outcomeTwin_simple_const S supp Mabs c hc).B_nonneg

end Sieve.RunTwinSimpleConstDemo
