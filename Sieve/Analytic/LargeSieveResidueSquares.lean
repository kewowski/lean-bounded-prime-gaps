/-
  Sieve/Analytic/LargeSieveResidueSquares.lean

  A leaf-level alias of the toolbox large-sieve inequality in the exact
  residue-filtered shape we use downstream. This keeps the shape pinned
  and avoids callers reaching into the toolbox directly.
-/
import Mathlib
import Sieve.Analytic.BVToolboxProgressionsSig

noncomputable section
open Classical

namespace Sieve
namespace Analytic

/-- **Large sieve (residue squares, filtered form).**
For any `a : ℕ → ℝ` supported on `[0..N]`,
\[
  \sum_{r<q} \Big(\sum_{n\le N,\ n\bmod q=r} a(n)\Big)^2
  \ \le\ \mathrm{C\_LS}\ \sum_{n\le N} a(n)^2 .
\]
This is just `TB.large_sieve_progressions` re-exposed with a stable name. -/
lemma large_sieve_residue_squares
    (TB : BVToolboxProgressionsSig) (q N : ℕ) (a : ℕ → ℝ) :
    (∑ r ∈ Finset.range q,
        (∑ n ∈ (Finset.range (N + 1)).filter (fun n => n % q = r), a n) ^ 2)
      ≤ TB.C_LS * (∑ n ∈ Finset.range (N + 1), (a n) ^ 2) :=
  TB.large_sieve_progressions q N a

/-- Tiny compile-touch to keep this surface hot. -/
theorem ls_residue_squares_compiles (TB : BVToolboxProgressionsSig) : True := by
  let _ := large_sieve_residue_squares TB 3 5 (fun n => (n : ℝ))
  exact True.intro

end Analytic
end Sieve
