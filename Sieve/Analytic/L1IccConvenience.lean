/-
  Sieve/Analytic/L1IccConvenience.lean
  L¹ bounds over the subrange `q ∈ [1, Q]`, derived from the CS+large-sieve
  L² packaging. Keeps constants explicit and proofs lightweight.

  Result:
    ∑_{q=1}^Q ∑_{r mod q+1} ‖residueSum a N q r‖
      ≤ (Q+1) * √( C_ls * (N + Q^2) * ∑_{n=1}^N ‖a n‖² ).
-/
import Mathlib
import Sieve.Analytic.LargeSieveCore
import Sieve.Analytic.IndexCounting
import Sieve.Analytic.L1FromCS

noncomputable section
open Classical BigOperators

namespace Sieve
namespace Analytic

/--
L¹ packaging over the index subrange `q ∈ [1, Q]`.

We compare the subrange to `range (Q+1)` by subset inclusion and nonnegativity,
then plug the toolbox CS+large-sieve bridge on the larger index set.
-/
theorem L1_over_Icc1Q_from_CS_and_LS
    (T : BVToolbox) (a : ℕ → ℂ) {N Q : ℕ}
    (hN : 1 ≤ N) (hQ : 1 ≤ Q) :
    (∑ q ∈ Finset.Icc 1 Q,
       ∑ r : ZMod q.succ, ‖residueSum a N q r‖)
    ≤ ((Q + 1 : ℕ) : ℝ)
      * Real.sqrt
          (T.C_ls * (N + Q^2) * (∑ n ∈ Finset.Icc 1 N, ‖a n‖^2)) := by
  -- Define per-modulus L¹ mass; it is pointwise ≥ 0.
  let f : ℕ → ℝ := fun q => ∑ r : ZMod q.succ, ‖residueSum a N q r‖
  have f_nonneg : ∀ q, 0 ≤ f q := by
    intro q
    classical
    unfold f
    refine Finset.sum_nonneg ?h
    intro r _
    simpa using (norm_nonneg (residueSum a N q r))
  -- `[1, Q] ⊆ range (Q+1)`.
  have hSubset : Finset.Icc 1 Q ⊆ Finset.range (Q + 1) := by
    intro q hq
    rcases Finset.mem_Icc.mp hq with ⟨_hq1, hqQ⟩
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le hqQ)
  -- Monotonicity of sums of nonnegative terms under subset inclusion.
  have h_sub_le :
      (∑ q ∈ Finset.Icc 1 Q, f q)
        ≤ (∑ q ∈ Finset.range (Q + 1), f q) :=
    Finset.sum_le_sum_of_subset_of_nonneg
      hSubset
      (by
        intro q _hq _hnotmem
        exact f_nonneg q)
  -- Bound the larger-range L¹ mass via the CS+large-sieve bridge.
  have h_L1_big :=
    L1_from_CS_and_LS T a hN hQ
  -- Conclude by transitivity and unfolding `f`.
  simpa [f] using le_trans h_sub_le h_L1_big

end Analytic
end Sieve

