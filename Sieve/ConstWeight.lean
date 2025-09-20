/-
  Sieve/ConstWeight.lean
  UTF-8 (no BOM), ASCII-only.

  A basic constant weight on a chosen finite support.
-/
import Mathlib
import Sieve.MaynardWeights

noncomputable section
open Classical

namespace Sieve.ConstWeight

/-- Build a weight that takes the constant value `c` (with `c ≥ 0`) everywhere,
    and whose finite summation support is exactly `supp`. -/
def const (supp : Finset Int) (c : ℝ) (hc : 0 ≤ c) : Sieve.MaynardWeights.Weight :=
  { w := fun _ => c
    support := supp
    nonneg := by intro _; exact hc
    bounded := by
      refine ⟨c, hc, ?_⟩
      intro _
      have : |c| = c := abs_of_nonneg hc
      simp [this]
    norm1 := True
    norm2 := True }

end Sieve.ConstWeight

