/-
  Sieve/GallagherHookSimple.lean
  A drop-in hook exposing the simple abs-window Gallagher contract.
-/
import Mathlib
import Sieve.LinearSieveBounds
import Sieve.GallagherSimple

noncomputable section
open Classical

namespace Sieve.GallagherHookSimple

/-- Export a simple, non-zero Gallagher contract from a chosen window `S` and cap `Mabs`. -/
def contract (S : Finset ℤ) (Mabs : ℝ) : Sieve.LinearSieveBounds.SieveContract :=
{ gallagher := Sieve.GallagherSimple.bound_of_absWindow S Mabs }

end Sieve.GallagherHookSimple
