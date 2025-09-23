/-
  Sieve/Analytic/SumSwapResidues.lean
  L¹ bound when summing over *all* residue classes.

  Main result:
    `sum_residueL1_le_qsucc_sumNorm` :
      ∑_{r mod q+1} ‖residueSum a N q r‖
        ≤ (q+1) · ∑_{n=1}^N ‖a n‖.

  This avoids any fragile sum-swapping; it just applies the triangle
  inequality pointwise and sums the resulting constant bound.
-/
import Mathlib
import Sieve.Analytic.ResidueSumBasics

noncomputable section
open Classical BigOperators

namespace Sieve
namespace Analytic

/--
L¹ bound after summing over all residue classes:

  ∑_{r mod q+1} ‖residueSum a N q r‖
    ≤ (q+1) * ∑_{n=1}^N ‖a n‖.
-/
theorem sum_residueL1_le_qsucc_sumNorm
    (a : ℕ → ℂ) (N q : ℕ) :
    (∑ r : ZMod q.succ, ‖residueSum a N q r‖)
      ≤ ((q.succ : ℕ) : ℝ) * (∑ n ∈ Finset.Icc 1 N, ‖a n‖) := by
  classical
  -- Pointwise triangle inequality.
  have hpt :
      ∀ r : ZMod q.succ,
        ‖residueSum a N q r‖ ≤ (∑ n ∈ Finset.Icc 1 N, ‖a n‖) := by
    intro r; exact norm_residueSum_le_sum_norm a N q r
  -- Sum the pointwise bounds.
  have hsum :
      (∑ r : ZMod q.succ, ‖residueSum a N q r‖)
        ≤ (∑ _r : ZMod q.succ, (∑ n ∈ Finset.Icc 1 N, ‖a n‖)) :=
    Finset.sum_le_sum (fun r _ => hpt r)
  -- Evaluate the constant sum over residues.
  simpa [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using hsum

end Analytic
end Sieve
