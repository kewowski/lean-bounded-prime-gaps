import Character.Decompositions
import Character.Lifting

/-
Character/Prime.lean
--------------------
Minimal, safe helpers for restricting to primes, built on the `mask` machinery.
-/

namespace Character

open scoped BigOperators
open Finset

/-- Keep only prime-indexed entries of a sequence. -/
def primeMask (a : ℕ → ℂ) : ℕ → ℂ := fun n => if Nat.Prime n then a n else 0

/-- Restricting to prime indices does not increase the truncated l² mass. -/
lemma l2NormSq_primes_le (N : ℕ) (a : ℕ → ℂ) :
  l2NormSq N (primeMask a) ≤ l2NormSq N a := by
  classical
  simpa [primeMask] using
    (l2NormSq_mask_le N a (P := Nat.Prime))

end Character
