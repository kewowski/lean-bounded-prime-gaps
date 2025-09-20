/-
  Sieve/GallagherSimple.lean
  A simple, character-free Gallagher bound:
  B := (|S|)^2 · M^2  (always nonnegative).
-/
import Mathlib
import Sieve.LinearSieveBounds

noncomputable section
open Classical

namespace Sieve.GallagherSimple

/-- Simple Gallagher bound from a finite window `S` and an abs cap `M`. -/
def bound_of_absWindow (S : Finset ℤ) (M : ℝ) :
    Sieve.LinearSieveBounds.GallagherBound :=
{ name   := "abs-sum-square window bound"
, B      := (S.card : ℝ)^2 * M^2
, nonneg := by
    -- squares are nonnegative; product of nonnegatives is nonnegative
    exact mul_nonneg (sq_nonneg _) (sq_nonneg _) }

/-- Package it as a `SieveContract`. -/
def contract_of_absWindow (S : Finset ℤ) (M : ℝ) :
    Sieve.LinearSieveBounds.SieveContract :=
{ gallagher := bound_of_absWindow S M }

end Sieve.GallagherSimple
