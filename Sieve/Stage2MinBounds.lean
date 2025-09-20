/-
  Sieve/Stage2MinBounds.lean
  Combine first- and second-moment heavy bounds into a single `min` form.
-/
import Mathlib
import Sieve.MaynardWeights
import Sieve.MTMoments
import Sieve.Stage2Thresholds
import Sieve.Stage2SecondMoment
import Sieve.Stage2Density
import Sieve.Stage2DensitySecond

noncomputable section
open Classical BigOperators

namespace Sieve
namespace Stage2

/-- Count bound: for `τ > 0` and any `M` with
`∑ w ≤ |support| * M`, we have
`heavy_count(τ) ≤ min (|support| * M / τ) (secondMoment / τ^2)`. -/
theorem heavy_count_le_min_of_first_and_second
    (W : Sieve.MaynardWeights.Weight) {M τ : ℝ}
    (hτpos : 0 < τ)
    (h_first : (∑ n ∈ W.support, W.w n) ≤ (W.support.card : ℝ) * M) :
    ((W.support.filter (fun n => τ ≤ W.w n)).card : ℝ)
      ≤ min ((W.support.card : ℝ) * M / τ)
            (Sieve.MTMoments.secondMoment W / (τ^2)) := by
  refine le_min ?h_first ?h_second
  · -- Markov / first-moment
    simpa using
      Sieve.Stage2.heavy_count_le_of_firstMoment
        (W := W) (M := M) (τ := τ) hτpos h_first
  · -- Chebyshev / second-moment
    simpa using
      Sieve.Stage2SecondMoment.heavy_count_le_of_secondMoment
        (W := W) hτpos

/-- Density bound: if `0 < |support|` and `τ > 0` and
`∑ w ≤ |support| * M`, then
`heavy_density(τ) ≤ min (M / τ) (secondMoment / (τ^2 * |support|))`. -/
theorem heavy_density_le_min_of_first_and_second
    (W : Sieve.MaynardWeights.Weight) {M τ : ℝ}
    (hpos : 0 < W.support.card)
    (hτpos : 0 < τ)
    (h_first : (∑ n ∈ W.support, W.w n) ≤ (W.support.card : ℝ) * M) :
    ((W.support.filter (fun n => τ ≤ W.w n)).card : ℝ) / (W.support.card : ℝ)
      ≤ min (M / τ)
            (Sieve.MTMoments.secondMoment W / (τ^2 * (W.support.card : ℝ))) := by
  refine le_min ?h1 ?h2
  · -- density from first moment
    simpa using
      Sieve.Stage2.heavy_density_le_of_firstMoment
        (W := W) (M := M) (τ := τ) hpos hτpos h_first
  · -- density from second moment
    simpa using
      Sieve.Stage2.heavy_density_le_of_secondMoment
        (W := W) (τ := τ) hpos hτpos

end Stage2
end Sieve
