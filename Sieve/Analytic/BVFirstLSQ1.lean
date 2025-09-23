/-
  Sieve/Analytic/BVFirstLSQ1.lean
  UTF-8 (no BOM), ASCII-only.

  Content:
  - Specialize the toolbox large-sieve inequality to q = 1.
  - This yields: (∑ a)^2 ≤ C_LS * ∑ a^2 over [0..N].
  - Includes a tiny demo to keep the surface "hot".
-/
import Mathlib
import Sieve.Analytic.BVToolboxProgressionsSig

noncomputable section
open Classical

namespace Sieve
namespace Analytic

/-- For `q = 1`, the residue filter is the full range, since `n % 1 = 0` always. -/
lemma filter_mod_one_eq_range (N : ℕ) :
    (Finset.range (N + 1)).filter (fun n => n % 1 = 0)
      = Finset.range (N + 1) := by
  classical
  -- `Nat.mod_one n` rewrites `n % 1` to `0`, so the predicate simplifies to `True`.
  -- Then `Finset.filter (fun _ => True) s = s`.
  simp [Nat.mod_one]

/-- Sum over `Finset.range 1` picks out the single `r = 0` term. -/
lemma sum_range_one {β} [AddCommMonoid β] (f : ℕ → β) :
    ∑ r ∈ Finset.range 1, f r = f 0 := by
  classical
  simp [Finset.range_one]

/-- **q = 1 large-sieve specialization.**
`(∑ a)^2 ≤ C_LS * ∑ a^2` on `[0..N]`. -/
lemma large_sieve_q1_square_bound
    (TB : BVToolboxProgressionsSig) (N : ℕ) (a : ℕ → ℝ) :
    ( (∑ n ∈ Finset.range (N + 1), a n) ) ^ 2
      ≤ TB.C_LS * (∑ n ∈ Finset.range (N + 1), (a n) ^ 2) := by
  classical
  -- Start from the toolbox inequality and simplify the LHS at q = 1.
  -- LHS: sum over r ∈ range 1 of the squared residue-block sum.
  -- `range 1` is `{0}`, and the residue filter is the whole range.
  have h := TB.large_sieve_progressions (q := 1) N a
  -- Simplify the residue sum at q = 1
  -- Note: the `filter` is the whole `range (N+1)`, so we collapse the inner sum.
  -- Then `sum over r ∈ range 1` collapses to the single `r = 0` term.
  simpa [sum_range_one, filter_mod_one_eq_range] using h

/-- Tiny "hot path" touch so CI watches this specialization. -/
theorem ls_q1_demo (TB : BVToolboxProgressionsSig) : True := by
  classical
  let _ := large_sieve_q1_square_bound TB 5 (fun n => (n : ℝ))
  exact True.intro

end Analytic
end Sieve
