/-
  Sieve/Analytic/ResidueL1TrivialBounds.lean
  Unweighted L¹ trivial bound re-exposed via the `residueL1` definition.
-/
import Mathlib
import Sieve.Analytic.ResidueSumBasics
import Sieve.Analytic.DataMassBasics
import Sieve.Analytic.SumSwapResidues

noncomputable section
open Classical BigOperators

namespace Sieve
namespace Analytic

/--
Trivial L¹ bound (unweighted) in terms of `residueL1`:

  `residueL1 a N q ≤ (q+1) * ∑_{n=1}^N ‖a n‖`.
-/
theorem residueL1_le_qsucc_sumNorm_trivial
    (a : ℕ → ℂ) (N q : ℕ) :
    residueL1 a N q ≤ ((q.succ : ℕ) : ℝ) * (∑ n ∈ Finset.Icc 1 N, ‖a n‖) := by
  simpa [residueL1] using (sum_residueL1_le_qsucc_sumNorm a N q)

end Analytic
end Sieve
