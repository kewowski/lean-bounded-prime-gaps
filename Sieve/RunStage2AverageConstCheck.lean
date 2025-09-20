/-
  Sieve/RunStage2AverageConstCheck.lean
  Check: for a constant weight on a nonempty window, the Stage-1 average bound gives c ≤ M.
-/
import Mathlib
import Sieve.AdmissibleTwin
import Sieve.ConstWeight
import Sieve.ConstWeightAverage
import Sieve.OutcomeBuilders
import Sieve.Stage2Average
import Sieve.PipelineSimp
import Sieve.MTMoments

noncomputable section
open Classical

namespace Sieve.RunStage2AverageConstCheck

def window (M : ℕ) : Finset ℤ := Finset.Icc (-(M : ℤ)) (M : ℤ)

example (M : ℕ) (c : ℝ) (hc : 0 ≤ c) :
    let cfg  := Sieve.AdmissibleTwin.twinConfig
    let supp := window M
    let W    := Sieve.ConstWeight.const supp c hc
    let out  := Sieve.OutcomeBuilders.outcome_const_with_cfg cfg supp c hc
    c ≤ out.M := by
  intro cfg supp W out
  -- support is nonempty since 0 ∈ [-M, M]
  have hz_le : (0 : ℤ) ≤ (M : ℤ) := by exact_mod_cast (Nat.zero_le M)
  have hz_ge : (-(M : ℤ)) ≤ 0   := by exact neg_nonpos.mpr hz_le
  have hmem : (0 : ℤ) ∈ supp   := by exact Finset.mem_Icc.mpr ⟨hz_ge, hz_le⟩
  have hpos_supp : 0 < supp.card := Finset.card_pos.mpr ⟨0, hmem⟩
  -- Stage-1 average bound: (∑ W.w)/|supp| ≤ M
  have havg : (∑ n ∈ W.support, W.w n) / (W.support.card : ℝ) ≤ out.M := by
    have hposW : 0 < W.support.card := by simpa [W, Sieve.ConstWeight.const] using hpos_supp
    simpa using Sieve.Stage2.avg_first_le_of_outcome cfg W out hposW
  -- For constant weights, the average equals c.
  have avg_eq : (∑ n ∈ W.support, W.w n) / (W.support.card : ℝ) = c := by
    -- use the exact constant-weight average lemma
    simpa [Sieve.MTMoments.firstMoment, W, Sieve.ConstWeight.const]
      using Sieve.ConstWeight.avg_first_const supp c hc hpos_supp
  -- Done.
  simpa [avg_eq] using havg

end Sieve.RunStage2AverageConstCheck
