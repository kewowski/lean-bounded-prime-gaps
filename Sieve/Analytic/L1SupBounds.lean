/-
  Sieve/Analytic/L1SupBounds.lean
  Simple "sup" bounds for the L¹ mass over residue classes.
-/
import Mathlib
import Sieve.Analytic.ResidueSumBasics
import Sieve.Analytic.DataMassBasics

noncomputable section
open Classical BigOperators

namespace Sieve
namespace Analytic

/--
If every residue sum has norm at most `M`, then the L¹ mass is at most
`(card residues) * M`.

Formally:
  (∀ r, ‖residueSum a N q r‖ ≤ M) →
    residueL1 a N q ≤ (Fintype.card (ZMod q.succ)) * M.
-/
theorem residueL1_le_card_mul_of_pointwise_le
    (a : ℕ → ℂ) (N q : ℕ) {M : ℝ}
    (h : ∀ r : ZMod q.succ, ‖residueSum a N q r‖ ≤ M) :
    residueL1 a N q ≤ ((Fintype.card (ZMod q.succ) : ℕ) : ℝ) * M := by
  classical
  -- Sum the pointwise bounds over `r : ZMod (q+1)`.
  have :
      (∑ r : ZMod q.succ, ‖residueSum a N q r‖)
        ≤ (∑ _r : ZMod q.succ, M) :=
    Finset.sum_le_sum (fun r _ => h r)
  -- Evaluate the constant sum on the right.
  simpa [residueL1, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using this

end Analytic
end Sieve
