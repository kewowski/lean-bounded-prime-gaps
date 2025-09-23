/-
  Sieve/Analytic/DPSAliases.lean

  Discrete Partial Summation (DPS) aliases in the exact shapes we use:
  (1) `dps_eq`         : direct alias of the toolbox equality.
  (2) `dps_flip_tail`  : writes the tail as `+ ( - ∑ (A (n+1) - A n))`.

  Leaf-level helpers (no heavy analysis).
-/
import Mathlib
import Sieve.Analytic.BVToolboxProgressionsSig

noncomputable section
open Classical

namespace Sieve
namespace Analytic

/-- DPS alias (shape from the toolbox). -/
lemma dps_eq
    (TB : BVToolboxProgressionsSig) (N : ℕ) (a A : ℕ → ℝ) :
    (∑ n ∈ Finset.range (N + 1), a n)
      = A N - A 0 + (∑ n ∈ Finset.range N, (A n - A (n + 1))) :=
  TB.discrete_partial_summation N a A

/-- DPS variant: flip the inner difference to `A (n+1) - A n` and factor a minus outside the sum. -/
lemma dps_flip_tail
    (TB : BVToolboxProgressionsSig) (N : ℕ) (a A : ℕ → ℝ) :
    (∑ n ∈ Finset.range (N + 1), a n)
      = A N - A 0 + ( - (∑ n ∈ Finset.range N, (A (n + 1) - A n)) ) := by
  classical
  -- Start from the toolbox equality.
  have h := dps_eq TB N a A
  -- Pointwise flip: `A n - A (n+1) = - (A (n+1) - A n)`.
  have hpt : ∀ n, (A n - A (n + 1)) = - (A (n + 1) - A n) := by
    intro n
    -- `neg_sub (A (n+1)) (A n) : -(A (n+1) - A n) = A n - A (n+1)`
    exact (neg_sub (A (n + 1)) (A n)).symm
  -- Pull the pointwise identity through the sum.
  have ht1 :
      (∑ n ∈ Finset.range N, (A n - A (n + 1)))
        = ∑ n ∈ Finset.range N, - (A (n + 1) - A n) := by
    refine Finset.sum_congr rfl ?_
    intro n hn
    exact hpt n
  -- Sum of negated terms equals the negated sum.
  have ht2 :
      (∑ n ∈ Finset.range N, - (A (n + 1) - A n))
        = - (∑ n ∈ Finset.range N, (A (n + 1) - A n)) :=
    Finset.sum_neg_distrib (s := Finset.range N) (f := fun n => A (n + 1) - A n)
  -- Replace the tail in `h` with the two equalities.
  rw [ht1, ht2] at h
  exact h

/-- Tiny compile-touch. -/
theorem dps_aliases_compiles (TB : BVToolboxProgressionsSig) : True := by
  let _ := dps_eq TB 0 (fun _ => (0 : ℝ)) (fun _ => (0 : ℝ))
  let _ := dps_flip_tail TB 0 (fun _ => (0 : ℝ)) (fun _ => (0 : ℝ))
  exact True.intro

end Analytic
end Sieve
