/-
  Sieve/Stage3HitCard.lean
  Identify window hit count with filtered cardinality.
-/
import Mathlib
import Sieve.Stage3PrimeFacade  -- for `hitIndicator`, `windowSum`, `windowHitCount`

noncomputable section
open Classical BigOperators

namespace Sieve
namespace Stage3

/-- The window hit *count* (sum of 0/1 indicators) equals the cardinality
of the filtered window. -/
theorem windowHitCount_eq_card_filter
    (H : Finset ℤ) (HS : HitSystem) (n : ℤ) :
    windowHitCount H HS n
      = ((H.filter (fun h => HS.isHit (n + h))).card : ℝ) := by
  classical
  -- unfold to the indicator sum over the window
  unfold windowHitCount windowSum hitIndicator
  -- swap sum of `ite` into sum over filtered set
  have hswap :
      (∑ h ∈ H, (if HS.isHit (n + h) then (1 : ℝ) else 0))
        = ∑ h ∈ H.filter (fun h => HS.isHit (n + h)), (1 : ℝ) :=
    (Finset.sum_filter (s := H) (p := fun h => HS.isHit (n + h))
                       (f := fun _ => (1 : ℝ))).symm
  -- sum of ones is the cardinality
  calc
    (∑ h ∈ H, (if HS.isHit (n + h) then (1 : ℝ) else 0))
        = ∑ h ∈ H.filter (fun h => HS.isHit (n + h)), (1 : ℝ) := hswap
    _   = ((H.filter (fun h => HS.isHit (n + h))).card : ℝ) := by
            simp [Finset.sum_const, nsmul_eq_mul, mul_comm]

end Stage3
end Sieve
