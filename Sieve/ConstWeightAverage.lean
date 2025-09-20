/-
  Sieve/ConstWeightAverage.lean
  For a constant weight on a nonempty support, the average first moment equals `c`.
-/
import Mathlib
import Sieve.ConstWeight
import Sieve.ConstWeightLemmas
import Sieve.MTMoments
import Sieve.PipelineSimp

noncomputable section
open Classical

namespace Sieve.ConstWeight

/-- For `const supp c hc`, if `supp` is nonempty then
    `firstMoment / (supp.card : ℝ) = c`. -/
lemma avg_first_const
    (supp : Finset ℤ) (c : ℝ) (hc : 0 ≤ c)
    (hpos : 0 < supp.card) :
    Sieve.MTMoments.firstMoment (const supp c hc) / (supp.card : ℝ) = c := by
  classical
  have h := Sieve.ConstWeight.firstMoment_const supp c hc
  have hcpos : 0 < (supp.card : ℝ) := by exact_mod_cast hpos
  have hcz : (supp.card : ℝ) ≠ 0 := ne_of_gt hcpos
  have := congrArg (fun x : ℝ => x / (supp.card : ℝ)) h
  simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc, hcz] using this

/-- Same equality, stated for Stage-1 hits via the definitional simp. -/
lemma avg_first_hits_const
    (cfg : Sieve.Pipeline.Config)
    (supp : Finset ℤ) (c : ℝ) (hc : 0 ≤ c)
    (hpos : 0 < supp.card) :
    (Sieve.Pipeline.stage1 cfg (const supp c hc)).hits.firstMomentLower
      / (supp.card : ℝ) = c := by
  simpa using avg_first_const supp c hc hpos

end Sieve.ConstWeight
