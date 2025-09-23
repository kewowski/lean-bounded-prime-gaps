/-
  Sieve/Analytic/L1ConstWeightConvenience.lean
  Specialize the weighted L¹ trivial bound to constant weights.
-/
import Mathlib
import Sieve.Analytic.ResidueSumBasics
import Sieve.Analytic.WeightedResidue
import Sieve.Analytic.WeightedResidueL1TrivialBounds

noncomputable section
open Classical BigOperators

namespace Sieve
namespace Analytic

/--
With constant weight `w n ≡ c`, the weighted L¹ bound simplifies to
  `∑_{r} ‖residueSumW a (const c) N q r‖
     ≤ (q+1)·|c| · ∑_{n=1}^N ‖a n‖`.
-/
theorem residueL1W_const_weight_bound
    (a : ℕ → ℂ) (c : ℝ) (N q : ℕ) :
    (∑ r : ZMod q.succ, ‖residueSumW a (fun _ => c) N q r‖)
      ≤ ((q.succ : ℕ) : ℝ) * |c| * (∑ n ∈ Finset.Icc 1 N, ‖a n‖) := by
  classical
  -- Start from the general weighted bound.
  have h :=
    residueL1W_le_qsucc_sum_absw_norm (a := a) (w := fun _ => c) (N := N) (q := q)
  -- Pull the constant `|c|` out of the `n`-sum.
  have hconst :
      (∑ n ∈ Finset.Icc 1 N, (|c| * ‖a n‖))
        = |c| * (∑ n ∈ Finset.Icc 1 N, ‖a n‖) := by
    simpa using
      (Finset.mul_sum (a := |c|)
        (s := Finset.Icc 1 N)
        (f := fun n => ‖a n‖)).symm
  -- Rewrite the right-hand side into the requested shape.
  have h' :
      (∑ r : ZMod q.succ, ‖residueSumW a (fun _ => c) N q r‖)
        ≤ ((q.succ : ℕ) : ℝ) * |c| * (∑ n ∈ Finset.Icc 1 N, ‖a n‖) := by
    simpa [hconst, mul_assoc] using h
  exact h'

end Analytic
end Sieve
