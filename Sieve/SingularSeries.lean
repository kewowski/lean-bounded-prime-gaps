/-
  Sieve/SingularSeries.lean
  UTF-8 (no BOM), ASCII-only.

  Minimal placeholder so downstream files can import and compile.
-/
import Mathlib

namespace Sieve

/-- Placeholder singular series normalisation. -/
def singularSeries (_H : Finset Nat) : Real := 1

@[simp] lemma singularSeries_nonneg (H : Finset Nat) : 0 ≤ singularSeries H := by
  -- Definitional reduction to 0 ≤ 1
  change 0 ≤ (1 : Real)
  exact zero_le_one

end Sieve
