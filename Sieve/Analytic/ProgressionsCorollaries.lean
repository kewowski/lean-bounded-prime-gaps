/-
  Sieve/Analytic/ProgressionsCorollaries.lean
  UTF-8 (no BOM), ASCII-only.

  Purpose
  -------
  Tiny convenience lemmas built *only* from the signatures in
  `BVToolboxProgressionsSig`. No heavy analysis — just algebraic rewrites
  and small corollaries that downstream Stage-3 wiring commonly needs.

  Contents
  • `large_sieve_total_bound`  — alias for the LS inequality (total sum of squares).
  • `dps_rearranged`           — discrete partial summation with a friendlier RHS order.

  House rules
  • Leaf module: import only what we need.
  • Use modern finset sum notation `∑ x ∈ s, f x`.
  • Keep proofs tiny (`simp`, `rw`, short `calc`).
-/
import Mathlib
import Sieve.Analytic.BVToolboxProgressionsSig

noncomputable section
open scoped BigOperators
open Finset

namespace Sieve
namespace Analytic

/-- Alias for the large-sieve inequality over residue-class sums. -/
lemma large_sieve_total_bound
    (TB : BVToolboxProgressionsSig) (q N : ℕ) (a : ℕ → ℝ) :
    (∑ r ∈ Finset.range q,
        (∑ n ∈ (Finset.range (N + 1)).filter (fun n => n % q = r), a n) ^ 2)
      ≤ TB.C_LS * (∑ n ∈ Finset.range (N + 1), (a n) ^ 2) :=
  TB.large_sieve_progressions q N a

/-- Discrete partial summation with a RHS order that is sometimes more convenient. -/
lemma dps_rearranged
    (TB : BVToolboxProgressionsSig) (N : ℕ) (a A : ℕ → ℝ) :
    (∑ n ∈ Finset.range (N + 1), a n)
      = A N + (∑ n ∈ Finset.range N, (A n - A (n + 1))) - A 0 := by
  classical
  -- Use the shape from the toolbox and reorder the RHS.
  have h := TB.discrete_partial_summation N a A
  -- Name the inner sum to make re-association clean.
  set S := ∑ n ∈ Finset.range N, (A n - A (n + 1)) with hS
  have h1 : (∑ n ∈ Finset.range (N + 1), a n) = A N - A 0 + S := by
    simpa [hS] using h
  -- Reassociate/commute to obtain `A N + S - A 0`.
  have h2 : A N - A 0 + S = A N + S - A 0 := by
    calc
      A N - A 0 + S
          = A N + (-A 0) + S := by simp [sub_eq_add_neg, add_assoc]
      _   = A N + ((-A 0) + S) := by simp [add_assoc]
      _   = A N + (S + (-A 0)) := by simp [add_comm]
      _   = A N + S + (-A 0) := by simp [add_assoc]
      _   = A N + S - A 0 := by simp [sub_eq_add_neg, add_assoc]
  exact h1.trans h2

/-- Availability sanity: touching the corollaries compiles fast. -/
theorem progressions_corollaries_wired
    (TB : BVToolboxProgressionsSig) : True := by
  classical
  let _ := large_sieve_total_bound TB 2 3 (fun n => (n : ℝ))
  let _ := dps_rearranged TB 0 (fun _ => (0 : ℝ)) (fun _ => (0 : ℝ))
  exact True.intro

end Analytic
end Sieve
