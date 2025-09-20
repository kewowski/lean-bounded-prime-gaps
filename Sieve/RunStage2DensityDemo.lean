/-
  Sieve/RunStage2DensityDemo.lean
  Demo: density bound of heavy points from an Outcome (conservative twins + const weight).
-/
import Mathlib
import Sieve.AdmissibleTwin
import Sieve.ConstWeight
import Sieve.OutcomeBuilders
import Sieve.Stage2Density

noncomputable section
open Classical

namespace Sieve.RunStage2DensityDemo

def window (M : ℕ) : Finset ℤ := Finset.Icc (-(M : ℤ)) (M : ℤ)

example (M : ℕ) (c τ : ℝ) (hc : 0 ≤ c) (hτ : 0 < τ) :
    let cfg  := Sieve.AdmissibleTwin.twinConfig
    let supp := window M
    let W    := Sieve.ConstWeight.const supp c hc
    let out  := Sieve.OutcomeBuilders.outcome_const_with_cfg cfg supp c hc
    0 < W.support.card →
    ((W.support.filter (fun n => τ ≤ W.w n)).card : ℝ)
/ (W.support.card : ℝ) ≤ out.M / τ := by
  intro cfg supp W out hpos
  -- show support is nonempty (0 ∈ [-M, M])
  have hz_le : (0 : ℤ) ≤ (M : ℤ) := by exact_mod_cast (Nat.zero_le M)
  have hz_ge : (-(M : ℤ)) ≤ 0   := by exact neg_nonpos.mpr hz_le
  have _ : (0 : ℤ) ∈ supp      := by exact Finset.mem_Icc.mpr ⟨hz_ge, hz_le⟩
  -- apply the density lemma
  simpa using
    Sieve.Stage2.heavy_density_le_of_outcome cfg W out hτ hpos

end Sieve.RunStage2DensityDemo
