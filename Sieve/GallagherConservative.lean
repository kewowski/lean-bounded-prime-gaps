/-
  Sieve/GallagherConservative.lean
  UTF-8 (no BOM), ASCII-only.

  Minimal conservative Gallagher bound export.
  This is a safe placeholder (B = 0) we can upgrade later.
-/
import Mathlib
import Sieve.LinearSieveBounds

noncomputable section
open Classical

namespace Sieve.GallagherConservative

/-- Conservative Gallagher bound constant for downstream use. -/
def bound : Sieve.LinearSieveBounds.GallagherBound :=
  { name := "GallagherConservative"
    B := 0
    nonneg := le_rfl }

end Sieve.GallagherConservative
