/-
  Sieve/Analytic/BVFirstPiecesChain.lean
  UTF-8 (no BOM), ASCII-only.

  Purpose:
  - Provide a minimal, concrete chain using the toolbox signatures:
      DPS (shape) → orthogonality (indicator) → large sieve (L² bound).
  - Keep it leaf-only and fast. These lemmas are *demonstrations* that the
    shapes line up; Stage-3 still consumes `AI_first` from BVFirstRealization.
-/
import Mathlib
import Sieve.Analytic.BVToolboxProgressionsSig

noncomputable section
open Classical

namespace Sieve
namespace Analytic

/-- Sum of `a` over the residue block `{n ≤ N | n % q = r}`. -/
def residueBlockSum (N q : ℕ) (r : ℕ) (a : ℕ → ℝ) : ℝ :=
  ∑ n ∈ (Finset.range (N + 1)).filter (fun n => n % q = r), a n

/-- The LS left-hand side is a sum of squares, hence nonnegative (toolbox-free). -/
lemma ls_sumSquares_nonneg (q N : ℕ) (a : ℕ → ℝ) :
    0 ≤ ∑ r ∈ Finset.range q, (residueBlockSum N q r a) ^ 2 := by
  classical
  have hterm : ∀ r ∈ Finset.range q, 0 ≤ (residueBlockSum N q r a) ^ 2 := by
    intro r _; exact sq_nonneg _
  exact Finset.sum_nonneg (by intro r hr; exact hterm r hr)

/-- Touch the orthogonality identity in exactly the toolbox’s shape. -/
lemma orthogonality_count_one
    (TB : BVToolboxProgressionsSig) (q r : ℕ) :
    (∑ n ∈ Finset.range q, (if n % q = r then (1 : ℝ) else 0))
      = (if r ∈ Finset.range q then (1 : ℝ) else 0) :=
  TB.orthogonality_indicator q r

/-- Touch the discrete partial summation identity (Abel transform shape). -/
lemma dps_touch
    (TB : BVToolboxProgressionsSig) (N : ℕ) (a A : ℕ → ℝ) :
    (∑ n ∈ Finset.range (N + 1), a n)
      = A N - A 0 + (∑ n ∈ Finset.range N, (A n - A (n + 1))) :=
  TB.discrete_partial_summation N a A

/-- Large sieve bound (constant-carrying) in the residue-block notation. -/
lemma ls_bound_touch
    (TB : BVToolboxProgressionsSig) (q N : ℕ) (a : ℕ → ℝ) :
    (∑ r ∈ Finset.range q, (residueBlockSum N q r a) ^ 2)
      ≤ TB.C_LS * (∑ n ∈ Finset.range (N + 1), (a n) ^ 2) := by
  -- This is exactly the toolbox inequality, just unfolding `residueBlockSum`.
  simpa [residueBlockSum] using TB.large_sieve_progressions q N a

/-- Minimal “chain wired” sanity: touch DPS, orthogonality, and LS once. -/
theorem first_chain_wired (TB : BVToolboxProgressionsSig) : True := by
  classical
  -- Orthogonality at a tiny instance
  have _ := orthogonality_count_one TB 3 1
  -- DPS at a tiny instance
  have _ := dps_touch TB 2 (fun _ => (0 : ℝ)) (fun _ => (0 : ℝ))
  -- LS at a tiny instance
  have _ := ls_bound_touch TB 2 3 (fun n => (n : ℝ))
  -- And a toolbox-free nonnegativity fact for the LS LHS
  have _ := ls_sumSquares_nonneg 2 3 (fun n => (n : ℝ))
  exact True.intro

end Analytic
end Sieve
