/-
  Sieve/Stage2SecondMoment.lean
  Chebyshev-style heavy-count bound from the second moment.

  Strategy:
  • Work over A := support.filter _ and use `sum_const`.
  • From (A.card)*τ^2 ≤ S, apply `div_le_div_of_nonneg_right` with τ^2 ≥ 0,
    then simplify the left via `mul_div_assoc` and `div_self`.
-/
import Mathlib
import Sieve.MaynardWeights
import Sieve.MTMoments

noncomputable section
open Classical BigOperators

namespace Sieve
namespace Stage2SecondMoment

/-- Chebyshev with squares:
`#{n ∈ support(W) | τ ≤ W.w n} ≤ secondMoment(W) / τ^2` for `τ > 0`. -/
theorem heavy_count_le_of_secondMoment
    (W : Sieve.MaynardWeights.Weight) {τ : ℝ} (hτpos : 0 < τ) :
    ((W.support.filter (fun n => τ ≤ W.w n)).card : ℝ)
      ≤ Sieve.MTMoments.secondMoment W / (τ^2) := by
  classical
  -- Notation.
  set s : Finset ℤ := W.support
  set A : Finset ℤ := s.filter (fun n => τ ≤ W.w n)

  have hτ0  : 0 ≤ τ := le_of_lt hτpos
  have hτ2pos : 0 < τ ^ 2 := by simpa [pow_two] using mul_pos hτpos hτpos
  have hτne  : τ ≠ 0 := ne_of_gt hτpos
  have hτ2ne : τ ^ 2 ≠ 0 := by simpa using pow_ne_zero (2 : ℕ) hτne

  -- Pointwise on A: τ^2 ≤ (W.w n)^2.
  have hpt : ∀ n ∈ A, τ ^ 2 ≤ (W.w n) ^ 2 := by
    intro n hnA
    rcases Finset.mem_filter.mp hnA with ⟨_, hτle⟩
    have h1 : τ * τ ≤ τ * W.w n := mul_le_mul_of_nonneg_left hτle hτ0
    have hw0 : 0 ≤ W.w n := W.nonneg n
    have h2 : τ * W.w n ≤ W.w n * W.w n := by
      simpa [mul_comm] using mul_le_mul_of_nonneg_right hτle hw0
    have : τ * τ ≤ W.w n * W.w n := le_trans h1 h2
    simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using this

  -- Sum over A: (A.card : ℝ) * τ^2 ≤ ∑_{A} (W.w n)^2.
  have h1 : (A.card : ℝ) * τ ^ 2 ≤ ∑ n ∈ A, (W.w n) ^ 2 := by
    have : ∑ n ∈ A, τ ^ 2 ≤ ∑ n ∈ A, (W.w n) ^ 2 :=
      Finset.sum_le_sum (by intro n hn; exact hpt n hn)
    simpa [Finset.sum_const, nsmul_eq_mul] using this

  -- Monotonicity A ⊆ s: ∑_{A} (W.w n)^2 ≤ ∑_{s} (W.w n)^2.
  have hsub : A ⊆ s := by
    intro n hnA; exact (Finset.mem_filter.mp hnA).1
  have h2 : ∑ n ∈ A, (W.w n) ^ 2 ≤ ∑ n ∈ s, (W.w n) ^ 2 := by
    refine Finset.sum_le_sum_of_subset_of_nonneg hsub ?_
    intro n hns _
    simpa using (sq_nonneg (W.w n))  -- 0 ≤ (W.w n)^2

  -- Chain: (A.card)*τ^2 ≤ S, where S := ∑_{s} (W.w n)^2.
  have chain : (A.card : ℝ) * τ ^ 2 ≤ ∑ n ∈ s, (W.w n) ^ 2 := le_trans h1 h2

  -- Divide both sides by τ^2 (order-preserving since τ^2 ≥ 0).
  have hdiv :
      ((A.card : ℝ) * τ ^ 2) / (τ ^ 2)
        ≤ (∑ n ∈ s, (W.w n) ^ 2) / (τ ^ 2) :=
    div_le_div_of_nonneg_right chain (le_of_lt hτ2pos)

  -- Simplify the left: ((A.card)*τ^2)/τ^2 = A.card.
  have : (A.card : ℝ) ≤ (∑ n ∈ s, (W.w n) ^ 2) / (τ ^ 2) := by
    simpa [mul_div_assoc, div_self hτ2ne, one_mul]
      using hdiv

  -- Final rewriting to secondMoment/τ^2 and names.
  simpa [Sieve.MTMoments.secondMoment, s, A] using this

end Stage2SecondMoment
end Sieve
