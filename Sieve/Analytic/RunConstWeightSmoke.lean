/-
  Sieve/Analytic/RunConstWeightSmoke.lean
  Tiny smoke test: constant-weight L¹ bound with `c = 1` reduces to the
  unweighted trivial bound.
-/
import Mathlib
import Sieve.Analytic.ResidueSumBasics
import Sieve.Analytic.WeightedResidue
import Sieve.Analytic.WeightedResidueConst
import Sieve.Analytic.WeightedResidueL1TrivialBounds
import Sieve.Analytic.L1ConstWeightConvenience

noncomputable section
open Classical BigOperators

namespace Sieve
namespace Analytic

/-- Smoke: plug `c = 1` into the constant-weight L¹ bound. -/
theorem const_one_matches_unweighted
    (a : ℕ → ℂ) (N q : ℕ) :
    (∑ r : ZMod q.succ, ‖residueSumW a (fun _ => (1 : ℝ)) N q r‖)
      ≤ ((q.succ : ℕ) : ℝ) * (∑ n ∈ Finset.Icc 1 N, ‖a n‖) := by
  -- Use the constant-weight convenience lemma and simplify.
  simpa [abs_one, one_mul, mul_left_comm, mul_assoc] using
    (residueL1W_const_weight_bound (a := a) (c := (1 : ℝ)) (N := N) (q := q))

end Analytic
end Sieve
