/-
  Sieve/Stage3Ergonomics.lean
  Small aliases/helpers for common Stage-3 patterns.
-/
import Mathlib
import Sieve.Stage3PrimesEndToEnd  -- brings in Stage-3 core + heavySet_nonempty_of_avg_ge

noncomputable section
open Classical

namespace Sieve
namespace Stage3

/-- Convenience alias for `heavySet_nonempty_of_avg_ge` with the same arguments. -/
theorem heavySet_nonempty_of_tau_le_avg
    (W : Sieve.MaynardWeights.Weight) (τ : ℝ)
    (hpos   : 0 < W.support.card)
    (hτleavg : τ ≤ (∑ m ∈ W.support, W.w m) / (W.support.card : ℝ)) :
    (Sieve.MTCore.heavySet W τ).Nonempty :=
  heavySet_nonempty_of_avg_ge (W := W) (τ := τ) hpos hτleavg

end Stage3
end Sieve
