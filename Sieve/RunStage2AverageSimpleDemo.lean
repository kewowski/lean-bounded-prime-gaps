/-
  Sieve/RunStage2AverageSimpleDemo.lean
  Demo: normalized (average) first-moment bound from an Outcome (simple Gallagher).
-/
import Mathlib
import Sieve.ConfigBuilders
import Sieve.AdmissibleTwin
import Sieve.ConstWeight
import Sieve.OutcomeBuilders
import Sieve.Stage2Average
import Sieve.Pipeline

noncomputable section
open Classical

namespace Sieve.RunStage2AverageSimpleDemo

/-- Symmetric integer window `[-M, M]` (cast-friendly). -/
def window (M : ℕ) : Finset ℤ :=
  Finset.Icc (-(M : ℤ)) (M : ℤ)

/-- The average first-moment hit is ≤ `M` from the Outcome (simple Gallagher). -/
example (M : ℕ) (Mabs c : ℝ) (hc : 0 ≤ c) :
    (Sieve.Pipeline.stage1
        (Sieve.ConfigBuilders.simple (window M) Mabs
          Sieve.AdmissibleTwin.twin Sieve.AdmissibleTwin.admissible_twin)
        (Sieve.ConstWeight.const (window M) c hc)).hits.firstMomentLower
      / ((window M).card : ℝ)
      ≤ (Sieve.OutcomeBuilders.outcome_const_with_cfg
            (Sieve.ConfigBuilders.simple (window M) Mabs
              Sieve.AdmissibleTwin.twin Sieve.AdmissibleTwin.admissible_twin)
            (window M) c hc).M := by
  -- shorthands
  let cfg  := Sieve.ConfigBuilders.simple (window M) Mabs
                Sieve.AdmissibleTwin.twin Sieve.AdmissibleTwin.admissible_twin
  let supp := window M
  let W    := Sieve.ConstWeight.const supp c hc
  let out  := Sieve.OutcomeBuilders.outcome_const_with_cfg cfg supp c hc
  -- `supp` is nonempty: 0 ∈ [-M,M]
  have hz_le : (0 : ℤ) ≤ (M : ℤ) := by exact_mod_cast (Nat.zero_le M)
  have hz_ge : (-(M : ℤ)) ≤ 0   := by exact neg_nonpos.mpr hz_le
  have hmem0 : (0 : ℤ) ∈ supp  := by exact Finset.mem_Icc.mpr ⟨hz_ge, hz_le⟩
  have hpos  : 0 < supp.card   := Finset.card_pos.mpr ⟨0, hmem0⟩
  -- apply the average bound
  simpa using Sieve.Stage2.avg_first_le_of_outcome cfg W out hpos

end Sieve.RunStage2AverageSimpleDemo
