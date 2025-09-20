/-
  Sieve/Stage3HitCardBounds.lean
  Cardinality bound: number of hits in a window is ≤ |H|.
-/
import Mathlib
import Sieve.Stage3PrimeFacade   -- windowSum/hitIndicator/windowHitCount
import Sieve.Stage3HitCard       -- windowHitCount_eq_card_filter
import Sieve.Stage3WindowBounds  -- windowHitCount_le_card

noncomputable section
open Classical BigOperators

namespace Sieve
namespace Stage3

/-- The number of hits in the window `H` at `n` is at most `|H|`. -/
theorem hits_card_le_window_size (H : Finset ℤ) (HS : HitSystem) (n : ℤ) :
    (H.filter (fun h => HS.isHit (n + h))).card ≤ H.card := by
  classical
  -- move to ℝ via our equalities/bounds and cast back down
  have hreal :
      ((H.filter (fun h => HS.isHit (n + h))).card : ℝ)
        ≤ (H.card : ℝ) := by
    -- left side = windowHitCount; right side ≥ windowHitCount (by earlier bound)
    have := Sieve.Stage3.windowHitCount_le_card (H := H) (HS := HS) (n := n)
    simpa [Sieve.Stage3.windowHitCount_eq_card_filter] using this
  exact_mod_cast hreal

end Stage3
end Sieve
