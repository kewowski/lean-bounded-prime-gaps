/-
  Sieve/Analytic/LargeSieveConvenience.lean
  Convenience corollaries around `BVToolbox.largeSieve_residueProgressions`,
  keeping proofs lightweight and compatible with Stage-3 consumers.
-/
import Mathlib
import Sieve.Analytic.LargeSieveCore

noncomputable section
open Classical BigOperators

namespace Sieve
namespace Analytic

/--
A clean subrange corollary: summing only over `q ∈ [1, Q]` is bounded
by the same `(N + Q^2)` RHS. This is immediate from the toolbox bound
over `q ∈ range (Q+1)` plus nonnegativity of the summands.
-/
theorem largeSieve_over_Icc1Q
    (T : BVToolbox) (a : ℕ → ℂ) {N Q : ℕ}
    (hN : 1 ≤ N) (hQ : 1 ≤ Q) :
    (∑ q ∈ Finset.Icc 1 Q,
       ∑ r : ZMod q.succ,
         ‖residueSum a N q r‖^2)
    ≤ T.C_ls * (N + Q^2) * (∑ n ∈ Finset.Icc 1 N, ‖a n‖^2) := by
  -- Define the per-modulus L² mass; it is pointwise ≥ 0.
  let f : ℕ → ℝ :=
    fun q => ∑ r : ZMod q.succ, ‖residueSum a N q r‖^2
  have f_nonneg : ∀ q, 0 ≤ f q := by
    intro q
    classical
    refine Finset.sum_nonneg ?pos
    intro r _
    -- Each term is a square of a norm in ℝ.
    simpa using (sq_nonneg (‖residueSum a N q r‖ : ℝ))
  -- `[1, Q] ⊆ range (Q+1)`.
  have hSubset : Finset.Icc 1 Q ⊆ Finset.range (Q + 1) := by
    intro q hq
    rcases Finset.mem_Icc.mp hq with ⟨_hq1, hqQ⟩
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le hqQ)
  -- Monotonicity of sums over nonnegative terms along subset inclusion.
  have h_sum_mono :
      (∑ q ∈ Finset.Icc 1 Q, f q)
        ≤ (∑ q ∈ Finset.range (Q + 1), f q) :=
    Finset.sum_le_sum_of_subset_of_nonneg
      hSubset
      (by
        intro q _hq _hnotmem
        exact f_nonneg q)
  -- Bind with the toolbox inequality on the larger index set.
  have h_ls :
      (∑ q ∈ Finset.range (Q + 1), f q)
        ≤ T.C_ls * (N + Q^2) * (∑ n ∈ Finset.Icc 1 N, ‖a n‖^2) :=
    by
      simpa using T.largeSieve_residueProgressions a hN hQ
  -- Conclude.
  exact le_trans h_sum_mono h_ls

end Analytic
end Sieve

