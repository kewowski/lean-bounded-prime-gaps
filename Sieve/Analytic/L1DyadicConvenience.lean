/-
  Sieve/Analytic/L1DyadicConvenience.lean
  L¹ bounds over a dyadic (or general) modulus window `q ∈ [Q₁, Q₂]`, via
  the CS + large-sieve packaging. Constants stay explicit and proofs are light.

  Result:
    ∑_{q=Q₁}^{Q₂} ∑_{r mod q+1} ‖residueSum a N q r‖
      ≤ (Q₂+1) * √( C_ls * (N + Q₂^2) * ∑_{n=1}^N ‖a n‖² ).
-/
import Mathlib
import Sieve.Analytic.LargeSieveCore
import Sieve.Analytic.L1FromCS

noncomputable section
open Classical BigOperators

namespace Sieve
namespace Analytic

/--
L¹ packaging over the dyadic subrange `q ∈ [Q₁, Q₂]`.

We majorize the subrange by `range (Q₂+1)` using subset inclusion and
nonnegativity, then apply `L1_from_CS_and_LS` with parameter `Q = Q₂`.
-/
theorem L1_over_IccQ1Q2_from_CS_and_LS
    (T : BVToolbox) (a : ℕ → ℂ) {N Q₁ Q₂ : ℕ}
    (hN : 1 ≤ N) (hQ12 : Q₁ ≤ Q₂) (hQ2 : 1 ≤ Q₂) :
    (∑ q ∈ Finset.Icc Q₁ Q₂,
       ∑ r : ZMod q.succ, ‖residueSum a N q r‖)
    ≤ ((Q₂ + 1 : ℕ) : ℝ)
      * Real.sqrt
          (T.C_ls * (N + Q₂^2) * (∑ n ∈ Finset.Icc 1 N, ‖a n‖^2)) := by
  -- Per-modulus L¹ mass (pointwise nonnegative).
  let f : ℕ → ℝ := fun q => ∑ r : ZMod q.succ, ‖residueSum a N q r‖
  have f_nonneg : ∀ q, 0 ≤ f q := by
    intro q
    classical
    unfold f
    refine Finset.sum_nonneg ?h
    intro r _
    simpa using (norm_nonneg (residueSum a N q r))
  -- `[Q₁, Q₂] ⊆ range (Q₂+1)`.
  have hSubset : Finset.Icc Q₁ Q₂ ⊆ Finset.range (Q₂ + 1) := by
    intro q hq
    rcases Finset.mem_Icc.mp hq with ⟨hq1, hq2⟩
    -- `q ≤ Q₂` gives `q < Q₂+1`.
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le hq2)
  -- Monotonicity of sums of nonnegative terms under subset inclusion.
  have h_sub_le :
      (∑ q ∈ Finset.Icc Q₁ Q₂, f q)
        ≤ (∑ q ∈ Finset.range (Q₂ + 1), f q) :=
    Finset.sum_le_sum_of_subset_of_nonneg
      hSubset
      (by
        intro q _hq _hnotmem
        exact f_nonneg q)
  -- Large-range L¹ via CS+large-sieve with `Q = Q₂`.
  have h_L1_big :
      (∑ q ∈ Finset.range (Q₂ + 1), f q)
        ≤ ((Q₂ + 1 : ℕ) : ℝ)
            * Real.sqrt
                (T.C_ls * (N + Q₂^2) * (∑ n ∈ Finset.Icc 1 N, ‖a n‖^2)) := by
    -- Reuse the packaged inequality; unfold `f`.
    simpa [f] using L1_from_CS_and_LS T a (N := N) (Q := Q₂) hN hQ2
  -- Conclude.
  exact le_trans h_sub_le h_L1_big

end Analytic
end Sieve

