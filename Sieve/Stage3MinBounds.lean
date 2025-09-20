/-
  Sieve/Stage3MinBounds.lean
  Stage-3 facing "min" bounds, framed via MTCore.heavyDensity.
-/
import Mathlib
import Sieve.MTCore
import Sieve.MTMoments
import Sieve.Stage2Exports
import Sieve.Stage2MinBounds

noncomputable section
open Classical BigOperators

namespace Sieve
namespace Stage3

/-- Density min bound (Stage-3 view).
If `0 < |support|`, `τ > 0` and `∑ w ≤ |support| * M` then
`heavyDensity(τ) ≤ min (M / τ) (secondMoment / (τ^2 * |support|))`. -/
theorem heavyDensity_le_min_MT
    (W : Sieve.MaynardWeights.Weight) {M τ : ℝ}
    (hpos : 0 < W.support.card) (hτpos : 0 < τ)
    (h_first : (∑ n ∈ W.support, W.w n) ≤ (W.support.card : ℝ) * M) :
    Sieve.MTCore.heavyDensity W τ
      ≤ min (M / τ)
            (Sieve.MTMoments.secondMoment W / (τ^2 * (W.support.card : ℝ))) := by
  classical
  -- Unfold density and combine the two Stage-2 density bounds with `le_min`.
  change
    ((W.support.filter (fun n => τ ≤ W.w n)).card : ℝ) / (W.support.card : ℝ)
      ≤ min (M / τ)
            (Sieve.MTMoments.secondMoment W / (τ^2 * (W.support.card : ℝ)))
  refine le_min ?h1 ?h2
  · simpa using
      Sieve.Stage2.heavy_density_le_of_firstMoment
        (W := W) (M := M) (τ := τ) hpos hτpos h_first
  · simpa using
      Sieve.Stage2.heavy_density_le_of_secondMoment
        (W := W) (τ := τ) hpos hτpos

end Stage3
end Sieve
