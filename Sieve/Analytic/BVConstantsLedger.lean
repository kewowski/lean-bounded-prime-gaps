/-
  Sieve/Analytic/BVConstantsLedger.lean
  Constants ledger for BV-style lower bounds with an explicit epsilon-loss.

  This extends `BVSketchParamsEps` with algebraic, assumption-friendly
  lemmas that let downstream analytic providers keep their hypotheses
  in a clean “main − (error pieces)/t” shape (e.g. with `t = log N`).

  Highlights:

    • `Cerr_add_eps_le_div`:
        If `Cerr ≤ A/t` and `eps ≤ B/t`, then `Cerr + eps ≤ (A+B)/t`.

    • `lowerFormulaParamsEps_ge_main_minus_div`:
        From the previous bound we get
          `Cmain - (A+B)/t ≤ lowerFormulaParamsEps P`.

  No heavy imports, no proofs deferred.
-/
import Mathlib
import Sieve.Analytic.BVSketchParamsEps

noncomputable section
open Classical

namespace Sieve
namespace Analytic

/--
If `P.Cerr ≤ A / t` and `P.eps ≤ B / t`, then the combined loss satisfies
`P.Cerr + P.eps ≤ (A + B) / t`.

This is purely algebraic (`/` is `* (t⁻¹)`), so it does not require `t ≠ 0`.
-/
lemma Cerr_add_eps_le_div
    (P : BVParamsEps) {A B t : ℝ}
    (hC : P.Cerr ≤ A / t) (hE : P.eps ≤ B / t) :
    P.Cerr + P.eps ≤ (A + B) / t := by
  -- Add the two bounds and rewrite `(A/t) + (B/t) = (A + B)/t`.
  have := add_le_add hC hE
  -- `(A/t) + (B/t) = (A + B)/t` since `/ t = * t⁻¹`.
  simpa [div_eq_mul_inv, mul_add, add_comm, add_left_comm, add_assoc]
    using this

/--
Lower-bound the main-minus-loss formula by grouping losses over a common divisor `t`.

If `P.Cerr ≤ A / t` and `P.eps ≤ B / t`, then
  `P.Cmain - (A + B) / t ≤ lowerFormulaParamsEps P`.

Equivalently:
  `P.Cmain - (A + B) / t ≤ P.Cmain - P.Cerr - P.eps`.
-/
lemma lowerFormulaParamsEps_ge_main_minus_div
    (P : BVParamsEps) {A B t : ℝ}
    (hC : P.Cerr ≤ A / t) (hE : P.eps ≤ B / t) :
    P.Cmain - (A + B) / t ≤ lowerFormulaParamsEps P := by
  -- From the split bounds, control the *sum* loss.
  have hsum : P.Cerr + P.eps ≤ (A + B) / t :=
    Cerr_add_eps_le_div P hC hE
  -- `a - y ≤ a - x` when `x ≤ y`; apply with `x = Cerr + eps`, `y = (A+B)/t`.
  have := sub_le_sub_left hsum P.Cmain
  -- Rewrite the target to the standard lower formula.
  simpa [lowerFormulaParamsEps_eq_main_sub_sum, sub_eq_add_neg,
         add_comm, add_left_comm, add_assoc] using this

end Analytic
end Sieve
