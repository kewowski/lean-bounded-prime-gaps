/-
  Sieve/Stage3AvgConst.lean
  Averaging a constant over a nonempty set (ℤ) gives the constant.
-/
import Sieve.Stage3Window

noncomputable section
open Classical BigOperators

namespace Sieve
namespace Stage3

/-- Average of a constant function over a nonempty finite set of integers. -/
theorem avgOver_const_int
    (A : Finset ℤ) (hA : A.Nonempty) (c : ℝ) :
    Sieve.Stage3.avgOver A (fun _ => c) = c := by
  classical
  have hpos : 0 < (A.card : ℝ) := by exact_mod_cast (Finset.card_pos.mpr hA)
  have hne  : (A.card : ℝ) ≠ 0 := ne_of_gt hpos
  have hsum : (∑ _a ∈ A, c) = (A.card : ℝ) * c := by
    simp [Finset.sum_const, nsmul_eq_mul, mul_comm]
  -- Multiply both sides by |A| and cancel the right factor.
  have hmul :
      Sieve.Stage3.avgOver A (fun _ => c) * (A.card : ℝ)
        = c * (A.card : ℝ) := by
    simp [Sieve.Stage3.avgOver, hsum, div_eq_mul_inv, hne,
          mul_comm]
  exact (mul_right_cancel₀ hne) hmul

/-- Specialization to the heavy set. -/
theorem avgOver_heavy_const
    (W : Sieve.MaynardWeights.Weight) (τ : ℝ)
    (hne : (Sieve.MTCore.heavySet W τ).Nonempty) (c : ℝ) :
    Sieve.Stage3.avgOver (Sieve.MTCore.heavySet W τ) (fun _ => c) = c := by
  classical
  exact avgOver_const_int (A := Sieve.MTCore.heavySet W τ) (hA := hne) (c := c)

end Stage3
end Sieve


