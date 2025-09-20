/-
  Sieve/Stage3SecondMomentEmptiness.lean
  Stage-3 wrappers: second-moment strict bound ⇒ heavy set empty ⇒ density = 0.
-/
import Mathlib
import Sieve.MTMoments
import Sieve.MTCore
import Sieve.Stage2Exports

noncomputable section
open Classical BigOperators

namespace Sieve
namespace Stage3

/-- If `secondMoment W < τ^2` (with `τ > 0`), the heavy set is empty. -/
theorem heavySet_eq_empty_of_secondMoment_lt
    (W : Sieve.MaynardWeights.Weight) {τ : ℝ}
    (hτpos : 0 < τ)
    (hSM : Sieve.MTMoments.secondMoment W < τ^2) :
    Sieve.MTCore.heavySet W τ = ∅ := by
  classical
  -- Use the Stage-2 emptiness corollary and rewrite to the Stage-3 heavy set.
  have := Sieve.Stage2.heavy_nonstrict_empty_of_secondMoment_lt
            (W := W) (τ := τ) hτpos hSM
  simpa [Sieve.MTCore.heavySet] using this

/-- If `secondMoment W < τ^2` (with `τ > 0`), the heavy density is `0`. -/
theorem heavyDensity_eq_zero_of_secondMoment_lt
    (W : Sieve.MaynardWeights.Weight) {τ : ℝ}
    (hτpos : 0 < τ)
    (hSM : Sieve.MTMoments.secondMoment W < τ^2) :
    Sieve.MTCore.heavyDensity W τ = 0 := by
  classical
  have hempty := heavySet_eq_empty_of_secondMoment_lt (W := W) (τ := τ) hτpos hSM
  -- Note: `0 / x = 0` in a field even if `x = 0`, so we don't need `|support| > 0` here.
  simp [Sieve.MTCore.heavyDensity, hempty]

end Stage3
end Sieve

