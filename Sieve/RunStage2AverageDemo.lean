/-
  Sieve/RunStage2AverageDemo.lean
  Demo: normalized (average) first-moment bound from an Outcome.
-/
import Mathlib
import Sieve.AdmissibleTwin
import Sieve.ConstWeight
import Sieve.OutcomeBuilders
import Sieve.Stage2Average
import Sieve.Pipeline

noncomputable section
open Classical

namespace Sieve.RunStage2AverageDemo

/-- Symmetric integer window `[-M, M]`. (use `(M : ℤ)` to keep casts painless) -/
def window (M : ℕ) : Finset ℤ :=
  Finset.Icc (-(M : ℤ)) (M : ℤ)

/-- The average first-moment hit is ≤ `M` from the Outcome (conservative twins). -/
example (M : ℕ) (c : ℝ) (hc : 0 ≤ c) :
    (Sieve.Pipeline.stage1 Sieve.AdmissibleTwin.twinConfig
        (Sieve.ConstWeight.const (window M) c hc)).hits.firstMomentLower
      / ((window M).card : ℝ)
      ≤ (Sieve.OutcomeBuilders.outcome_const_with_cfg
            Sieve.AdmissibleTwin.twinConfig (window M) c hc).M := by
  -- Shorthands
  let cfg := Sieve.AdmissibleTwin.twinConfig
  let supp := window M
  let W := Sieve.ConstWeight.const supp c hc
  let out := Sieve.OutcomeBuilders.outcome_const_with_cfg cfg supp c hc
  -- `supp` is nonempty (0 ∈ [-M, M]), hence card > 0
  have h₂ : (0 : ℤ) ≤ (M : ℤ) := by
    exact_mod_cast (Nat.zero_le M)
  have h₁ : (-(M : ℤ)) ≤ 0 := by
    exact neg_nonpos.mpr h₂
  have hmem0 : (0 : ℤ) ∈ supp := by
    exact Finset.mem_Icc.mpr ⟨h₁, h₂⟩
  have hpos : 0 < supp.card := Finset.card_pos.mpr ⟨0, hmem0⟩
  -- Apply the average bound
  simpa using
    Sieve.Stage2.avg_first_le_of_outcome cfg W out hpos

end Sieve.RunStage2AverageDemo
