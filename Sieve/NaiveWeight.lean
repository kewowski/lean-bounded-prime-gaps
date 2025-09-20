/-
  Sieve/NaiveWeight.lean
  UTF-8 (no BOM), ASCII-only.

  Provides a trivially valid Maynard–Tao weight to keep the pipeline runnable.
-/
import Mathlib
import Sieve.MaynardWeights

noncomputable section
open Classical

namespace Sieve.NaiveWeight

/-- The zero weight: `w n = 0` with empty support. -/
def zeroWeight : Sieve.MaynardWeights.Weight :=
  { w := fun _ => 0
    support := ({} : Finset Int)
    nonneg := by intro _; exact le_rfl
    bounded := by
      refine ⟨0, le_rfl, ?_⟩
      intro _; simp
    norm1 := True
    norm2 := True }

end Sieve.NaiveWeight
