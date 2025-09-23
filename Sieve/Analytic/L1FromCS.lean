/-
  Sieve/Analytic/L1FromCS.lean
  Cauchy–Schwarz packaging for residue sums:
  (1) A clean L¹ bound using only the CS field and index counting.
  (2) A generic bridge that swaps in any L² bound to yield an L¹ bound.
  (3) A specialization using the toolbox large-sieve field for the L² bound.

  All proofs are lightweight and rely on existing helpers.
-/
import Mathlib
import Sieve.Analytic.LargeSieveCore
import Sieve.Analytic.IndexCounting

noncomputable section
open Classical BigOperators

namespace Sieve
namespace Analytic

/--
L¹ control from CS and index counting (no L² estimate plugged yet):

  ∑_{q ≤ Q} ∑_{r mod q+1} ‖S(q,r)‖
    ≤ (Q+1) * √( ∑_{q ≤ Q} ∑_{r} ‖S(q,r)‖² ).

Here `S(q,r) = residueSum a N q r`.
-/
theorem L1_from_CS_indexOnly
    (T : BVToolbox) (a : ℕ → ℂ) {N Q : ℕ} (hN : 1 ≤ N) (hQ : 1 ≤ Q) :
    (∑ q ∈ Finset.range (Q + 1),
       ∑ r : ZMod q.succ, ‖residueSum a N q r‖)
    ≤ ((Q + 1 : ℕ) : ℝ)
      * Real.sqrt
          (∑ q ∈ Finset.range (Q + 1),
             ∑ r : ZMod q.succ, ‖residueSum a N q r‖^2) := by
  -- Toolbox CS field:
  have hCS := T.CS_residueL1_from_L2 a hN hQ
  -- √(index-size) ≤ (Q+1)
  have hIdx : Real.sqrt (∑ q ∈ Finset.range (Q + 1), ((q.succ : ℕ) : ℝ))
              ≤ ((Q + 1 : ℕ) : ℝ) :=
    sqrt_sum_qsucc_over_range_le_Qsucc Q
  -- Multiply the index bound by √(L²-mass) on the right.
  have hStep :
      Real.sqrt (∑ q ∈ Finset.range (Q + 1), ((q.succ : ℕ) : ℝ))
        * Real.sqrt
            (∑ q ∈ Finset.range (Q + 1),
               ∑ r : ZMod q.succ, ‖residueSum a N q r‖^2)
      ≤ ((Q + 1 : ℕ) : ℝ)
        * Real.sqrt
            (∑ q ∈ Finset.range (Q + 1),
               ∑ r : ZMod q.succ, ‖residueSum a N q r‖^2) := by
    refine mul_le_mul_of_nonneg_right hIdx ?nonneg
    exact Real.sqrt_nonneg _
  -- Chain the inequalities.
  exact le_trans hCS hStep

/--
Generic CS-bridge: if you have any upper bound `B` on the L²-mass over `(q,r)`,
you immediately get an L¹ bound with `(Q+1) * √B`.

`hB0` ensures we can apply `sqrt` monotonicity to `L² ≤ B`.
-/
theorem L1_from_CS_and_L2bound
    (T : BVToolbox) (a : ℕ → ℂ) {N Q : ℕ} (hN : 1 ≤ N) (hQ : 1 ≤ Q)
    {B : ℝ}
    (hL2_le : (∑ q ∈ Finset.range (Q + 1),
                 ∑ r : ZMod q.succ, ‖residueSum a N q r‖^2) ≤ B)
    (hB0 : 0 ≤ B) :
    (∑ q ∈ Finset.range (Q + 1),
       ∑ r : ZMod q.succ, ‖residueSum a N q r‖)
    ≤ ((Q + 1 : ℕ) : ℝ) * Real.sqrt B := by
  -- Start from the index-only CS bound.
  have h0 := L1_from_CS_indexOnly T a hN hQ
  -- Monotonicity: √(L²) ≤ √B.
  have hL2_nonneg :
      0 ≤ (∑ q ∈ Finset.range (Q + 1),
             ∑ r : ZMod q.succ, ‖residueSum a N q r‖^2) := by
    classical
    refine Finset.sum_nonneg ?h
    intro q hq
    refine Finset.sum_nonneg ?hr
    intro r _
    simpa using (sq_nonneg (‖residueSum a N q r‖ : ℝ))
  have hSqrt : Real.sqrt
      (∑ q ∈ Finset.range (Q + 1),
         ∑ r : ZMod q.succ, ‖residueSum a N q r‖^2)
      ≤ Real.sqrt B :=
    Real.sqrt_le_sqrt (by exact hL2_le)
  -- Strengthen the RHS by replacing √(L²) with √B.
  have h1 :
      ((Q + 1 : ℕ) : ℝ)
        * Real.sqrt
            (∑ q ∈ Finset.range (Q + 1),
               ∑ r : ZMod q.succ, ‖residueSum a N q r‖^2)
      ≤ ((Q + 1 : ℕ) : ℝ) * Real.sqrt B := by
    have hQ1_nonneg : 0 ≤ ((Q + 1 : ℕ) : ℝ) := by exact_mod_cast (Nat.zero_le (Q + 1))
    exact mul_le_mul_of_nonneg_left hSqrt hQ1_nonneg
  -- Conclude by transitivity.
  exact le_trans h0 h1

/--
Specialization: plug the toolbox large-sieve L² bound into the CS-bridge to
get a fully packaged L¹ bound depending only on `C_ls`, `N`, `Q`, and the
data mass of `a` up to `N`.
-/
theorem L1_from_CS_and_LS
    (T : BVToolbox) (a : ℕ → ℂ) {N Q : ℕ} (hN : 1 ≤ N) (hQ : 1 ≤ Q) :
    (∑ q ∈ Finset.range (Q + 1),
       ∑ r : ZMod q.succ, ‖residueSum a N q r‖)
    ≤ ((Q + 1 : ℕ) : ℝ)
      * Real.sqrt
          (T.C_ls * (N + Q^2) * (∑ n ∈ Finset.Icc 1 N, ‖a n‖^2)) := by
  -- The large-sieve L² bound:
  have hLS :=
    (T.largeSieve_residueProgressions a hN hQ)
  -- RHS nonnegativity for sqrt monotonicity:
  have hB0 :
      0 ≤ T.C_ls * (N + Q^2) * (∑ n ∈ Finset.Icc 1 N, ‖a n‖^2) := by
    have hC : 0 ≤ T.C_ls := le_trans (by norm_num : (0 : ℝ) ≤ 1) T.C_ls_pos
    have hNQ : 0 ≤ ((N + Q^2 : ℕ) : ℝ) := by exact_mod_cast (Nat.zero_le (N + Q^2))
    have hMass : 0 ≤ (∑ n ∈ Finset.Icc 1 N, ‖a n‖^2) := by
      classical
      refine Finset.sum_nonneg ?hn
      intro n _
      have : 0 ≤ ‖a n‖ := norm_nonneg _
      have : 0 ≤ ‖a n‖^2 := by simpa using sq_nonneg (‖a n‖ : ℝ)
      simpa using this
    exact mul_nonneg (mul_nonneg hC hNQ) hMass
  -- Apply the generic bridge with `B = C_ls * (N + Q^2) * ...`.
  simpa using
    L1_from_CS_and_L2bound T a hN hQ (B :=
      T.C_ls * (N + Q^2) * (∑ n ∈ Finset.Icc 1 N, ‖a n‖^2)) hLS hB0

end Analytic
end Sieve

