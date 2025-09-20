/-
  Sieve/Stage2Average.lean
  Average bound from an Outcome: (first hit)/(#support) ≤ M when the support is nonempty.
-/
import Mathlib
import Sieve.Pipeline
import Sieve.PipelineSimp
import Sieve.Stage2Basic
import Sieve.MaynardWeights

noncomputable section
open Classical

namespace Sieve.Stage2

/-- If `W.support` is nonempty, the Stage-1 first-moment hit average
    is bounded by `M` from an `Outcome W`. -/
lemma avg_first_le_of_outcome
    (cfg : Sieve.Pipeline.Config)
    (W   : Sieve.MaynardWeights.Weight)
    (out : Outcome W)
    (hpos : 0 < W.support.card) :
    (Sieve.Pipeline.stage1 cfg W).hits.firstMomentLower
      / (W.support.card : ℝ) ≤ out.M := by
  classical
  -- Start from the (unnormalized) first-moment bound
  have h := first_le_of_outcome cfg W out
  -- Denominator positivity and non-zeroness
  have hcpos : 0 < (W.support.card : ℝ) := by exact_mod_cast hpos
  have hcz   : (W.support.card : ℝ) ≠ 0 := ne_of_gt hcpos
  -- Multiply both sides by the nonnegative inverse
  have h' :
      ((W.support.card : ℝ)⁻¹) * (Sieve.Pipeline.stage1 cfg W).hits.firstMomentLower
        ≤ ((W.support.card : ℝ)⁻¹) * ((W.support.card : ℝ) * out.M) :=
    mul_le_mul_of_nonneg_left h (le_of_lt (inv_pos.mpr hcpos))
  -- Massage to the desired form
  simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc, hcz]
    using h'

/-- A convenient corollary: written with an explicit average on the LHS. -/
lemma first_avg_le_M_of_outcome
    (cfg : Sieve.Pipeline.Config)
    (W   : Sieve.MaynardWeights.Weight)
    (out : Outcome W)
    (hpos : 0 < W.support.card) :
    ((Sieve.Pipeline.stage1 cfg W).hits.firstMomentLower
      * (W.support.card : ℝ)⁻¹) ≤ out.M := by
  simpa [div_eq_mul_inv, mul_comm] using avg_first_le_of_outcome cfg W out hpos

end Sieve.Stage2
