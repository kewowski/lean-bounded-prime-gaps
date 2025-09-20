/-
  Sieve/LinearSieveBounds.lean
  UTF-8 (no BOM), ASCII-only.
-/
import Mathlib

noncomputable section
open Classical

namespace Sieve.LinearSieveBounds

/-- A named bound that Gallagher (or variants) provide for later stages. -/
structure GallagherBound where
  name   : String := "GallagherBound"
  B      : ℝ := 0
  nonneg : 0 ≤ B := by decide

/-- Downstream “contract” that bundles the pieces the MT pipeline uses. -/
structure SieveContract where
  gallagher : GallagherBound

end Sieve.LinearSieveBounds
