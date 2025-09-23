/-
  Sieve/Analytic/RunWeightedTrivialSmoke.lean
  Tiny smoke test for the weighted trivial L¹ bound.
-/
import Mathlib
import Sieve.Analytic.ResidueSumBasics
import Sieve.Analytic.WeightedResidue
import Sieve.Analytic.WeightedResidueL1TrivialBounds

noncomputable section
open Classical BigOperators

namespace Sieve
namespace Analytic

/-- Smoke: the weighted trivial L¹ bound as a one-liner. -/
theorem run_weighted_trivial_smoke
    (a : ℕ → ℂ) (w : ℕ → ℝ) (N q : ℕ) :
    (∑ r : ZMod q.succ, ‖residueSumW a w N q r‖)
      ≤ ((q.succ : ℕ) : ℝ) * (∑ n ∈ Finset.Icc 1 N, (|w n| * ‖a n‖)) :=
  residueL1W_le_qsucc_sum_absw_norm a w N q

end Analytic
end Sieve
