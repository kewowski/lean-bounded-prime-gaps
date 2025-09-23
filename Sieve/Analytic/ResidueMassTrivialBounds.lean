/-
  Sieve/Analytic/ResidueMassTrivialBounds.lean
  Trivial L² (mass) bounds for residue sums, using only triangle inequality.

  Main result:
    `residueMass_le_card_sumNorm_sq`:
      ∑_{r mod q+1} ‖residueSum a N q r‖²
        ≤ (card (ZMod (q+1))) · ( ∑_{n=1}^N ‖a n‖ )².

  We phrase the coefficient as `Fintype.card (ZMod q.succ)` to avoid relying
  on a specific lemma name for `card (ZMod n) = n`.
-/
import Mathlib
import Sieve.Analytic.ResidueSumBasics

noncomputable section
open Classical BigOperators

namespace Sieve
namespace Analytic

/--
Trivial L² mass bound from triangle inequality:

  ∑_{r mod q+1} ‖residueSum a N q r‖²
    ≤ (card (ZMod (q+1))) · ( ∑_{n=1}^N ‖a n‖ )².
-/
theorem residueMass_le_card_sumNorm_sq
    (a : ℕ → ℂ) (N q : ℕ) :
    (∑ r : ZMod q.succ, ‖residueSum a N q r‖^2)
      ≤ ((Fintype.card (ZMod q.succ) : ℕ) : ℝ)
          * (∑ n ∈ Finset.Icc 1 N, ‖a n‖)^2 := by
  classical
  -- Let S := ∑ ‖a n‖ and note S ≥ 0.
  have Snonneg : 0 ≤ (∑ n ∈ Finset.Icc 1 N, ‖a n‖) := by
    refine Finset.sum_nonneg ?_
    intro _ _; exact norm_nonneg _
  -- Pointwise: ‖S(q,r)‖ ≤ S ⇒ ‖S(q,r)‖² ≤ S² (both sides ≥ 0).
  have hpt :
      ∀ r : ZMod q.succ,
        ‖residueSum a N q r‖^2
          ≤ (∑ n ∈ Finset.Icc 1 N, ‖a n‖)^2 := by
    intro r
    have h := norm_residueSum_le_sum_norm a N q r
    have hx : 0 ≤ ‖residueSum a N q r‖ := norm_nonneg _
    -- Square both sides by multiplying the inequality with itself.
    have := mul_le_mul h h hx Snonneg
    simpa [pow_two] using this
  -- Sum the pointwise bounds and evaluate the constant sum.
  have :
      (∑ r : ZMod q.succ, ‖residueSum a N q r‖^2)
        ≤ (∑ _r : ZMod q.succ, (∑ n ∈ Finset.Icc 1 N, ‖a n‖)^2) :=
    Finset.sum_le_sum (fun r _ => hpt r)
  -- Turn the RHS into `(card) * S²`.
  simpa [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using this

end Analytic
end Sieve
