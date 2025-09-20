/-
  Sieve/Stage2Report.lean
  Small facade collecting easy-to-consume Stage 2 inequalities.
  Decoupled from any `Outcome` plumbing to keep things stable.
-/
import Mathlib
import Sieve.MaynardWeights
import Sieve.MTMoments
import Sieve.Stage2Squared
import Sieve.Stage2Thresholds
import Sieve.Stage2SecondMoment
import Sieve.Stage2Density

noncomputable section
open Classical BigOperators

namespace Sieve
namespace Stage2

/-- Square the average bound safely:
If `∑ w ≤ |support| * M` then `(∑ w)^2 ≤ |support|^2 * M^2`. -/
theorem first_sq_le_card_sq_mul_M_sq
    (W : Sieve.MaynardWeights.Weight) {M : ℝ}
    (h_first : (∑ n ∈ W.support, W.w n) ≤ (W.support.card : ℝ) * M) :
    (Sieve.MTMoments.firstMoment W) ^ 2
      ≤ (W.support.card : ℝ) ^ 2 * M ^ 2 := by
  simpa [Sieve.MTMoments.firstMoment]
    using Sieve.Stage2.rms_am_glue (W := W) (M := M) h_first

/-- Markov threshold bound:
If `∑ w ≤ |support| * M` and `τ > 0` then `heavy_count(τ) ≤ |support|*M/τ`. -/
theorem heavy_count_le_of_firstMoment'
    (W : Sieve.MaynardWeights.Weight) {M τ : ℝ}
    (hτpos : 0 < τ)
    (h_first : (∑ n ∈ W.support, W.w n) ≤ (W.support.card : ℝ) * M) :
    ((W.support.filter (fun n => τ ≤ W.w n)).card : ℝ)
      ≤ (W.support.card : ℝ) * M / τ :=
  Sieve.Stage2.heavy_count_le_of_firstMoment (W := W) (M := M) (τ := τ) hτpos h_first

/-- Chebyshev (second moment) bound:
If `τ > 0` then `heavy_count(τ) ≤ secondMoment/τ^2`. -/
theorem heavy_count_le_of_secondMoment'
    (W : Sieve.MaynardWeights.Weight) {τ : ℝ} (hτpos : 0 < τ) :
    ((W.support.filter (fun n => τ ≤ W.w n)).card : ℝ)
      ≤ Sieve.MTMoments.secondMoment W / (τ^2) :=
  Sieve.Stage2SecondMoment.heavy_count_le_of_secondMoment (W := W) hτpos

/-- Density version of the first-moment bound (needs `|support| > 0`). -/
theorem heavy_density_le_of_firstMoment'
    (W : Sieve.MaynardWeights.Weight) {M τ : ℝ}
    (hpos : 0 < W.support.card) (hτpos : 0 < τ)
    (h_first : (∑ n ∈ W.support, W.w n) ≤ (W.support.card : ℝ) * M) :
    ((W.support.filter (fun n => τ ≤ W.w n)).card : ℝ) / (W.support.card : ℝ)
      ≤ M / τ :=
  Sieve.Stage2.heavy_density_le_of_firstMoment (W := W) (M := M) (τ := τ) hpos hτpos h_first

end Stage2
end Sieve
