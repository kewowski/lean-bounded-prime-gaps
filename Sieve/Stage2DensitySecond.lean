/-
  Sieve/Stage2DensitySecond.lean
  Heavy-set density bound from the second moment.
-/
import Mathlib
import Sieve.MaynardWeights
import Sieve.MTMoments
import Sieve.Stage2SecondMoment

noncomputable section
open Classical BigOperators

namespace Sieve
namespace Stage2

/-- If `τ > 0` and `|support| > 0`, then
`density(τ-heavy) ≤ secondMoment / (τ^2 * |support|)`. -/
theorem heavy_density_le_of_secondMoment
    (W : Sieve.MaynardWeights.Weight) {τ : ℝ}
    (hpos : 0 < W.support.card) (hτpos : 0 < τ) :
    ((W.support.filter (fun n => τ ≤ W.w n)).card : ℝ) / (W.support.card : ℝ)
      ≤ Sieve.MTMoments.secondMoment W / (τ^2 * (W.support.card : ℝ)) := by
  classical
  set s : Finset ℤ := W.support
  have hscard_pos : 0 < (s.card : ℝ) := by exact_mod_cast hpos
  -- start from Chebyshev heavy-count bound
  have hcnt :
      ((s.filter (fun n => τ ≤ W.w n)).card : ℝ)
        ≤ Sieve.MTMoments.secondMoment W / (τ^2) :=
    Sieve.Stage2SecondMoment.heavy_count_le_of_secondMoment (W := W) hτpos
  -- divide both sides by |s| > 0
  have hdiv :
      ((s.filter (fun n => τ ≤ W.w n)).card : ℝ) / (s.card : ℝ)
        ≤ (Sieve.MTMoments.secondMoment W / (τ^2)) / (s.card : ℝ) :=
    div_le_div_of_nonneg_right hcnt (le_of_lt hscard_pos)
  -- reshape RHS: (A/|s|) ≤ secondMoment / (τ^2 * |s|)
  simpa [s, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
    using hdiv

end Stage2
end Sieve
