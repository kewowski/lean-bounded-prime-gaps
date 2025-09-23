/-
  Sieve/Analytic/LargeSieveWeightedConvenience.lean
  Convenience lemma for the weighted large-sieve inequality restricted to `q ∈ [1, Q]`.
  Uses nonnegativity + subset monotonicity to pass from `range (Q+1)` to `Icc 1 Q`.
-/
import Mathlib
import Sieve.Analytic.LargeSieveCore
import Sieve.Analytic.LargeSieveDefs

noncomputable section
open Classical BigOperators

namespace Sieve
namespace Analytic

/--
Weighted large-sieve over the subrange `q ∈ [1, Q]`.

If `0 ≤ w q ≤ 1` for all `q`, then
  ∑_{q=1}^Q w q * residueMass a N q
  ≤ C_ls * (N + Q^2) * ∑_{n=1}^N ‖a n‖².

This is an immediate corollary of the toolbox's weighted inequality over
`q ∈ range (Q+1)` by monotonicity of sums of nonnegative terms.
-/
theorem largeSieve_weighted_over_Icc1Q
    (T : BVToolbox) (a : ℕ → ℂ) (w : ℕ → ℝ) {N Q : ℕ}
    (hw : ∀ q, 0 ≤ w q ∧ w q ≤ 1)
    (hN : 1 ≤ N) (hQ : 1 ≤ Q) :
    (∑ q ∈ Finset.Icc 1 Q, w q * residueMass a N q)
      ≤ T.C_ls * (N + Q^2) * (∑ n ∈ Finset.Icc 1 N, ‖a n‖^2) := by
  -- Define the per-modulus weighted mass, pointwise nonnegative.
  let f : ℕ → ℝ := fun q => w q * residueMass a N q
  have f_nonneg : ∀ q, 0 ≤ f q := by
    intro q
    have hwq := hw q
    have hmass := residueMass_nonneg a N q
    exact mul_nonneg hwq.left hmass
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
  -- Bind with the toolbox weighted inequality on the larger index set.
  have h_ls :
      (∑ q ∈ Finset.range (Q + 1), f q)
        ≤ T.C_ls * (N + Q^2) * (∑ n ∈ Finset.Icc 1 N, ‖a n‖^2) := by
    simpa [f, residueMass] using
      (T.largeSieve_residueProgressions_weighted a w hw hN hQ)
  -- Conclude.
  exact le_trans h_sum_mono h_ls

end Analytic
end Sieve

