/-
  Sieve/GallagherHook.lean
  UTF-8 (no BOM), ASCII-only.

  Adapter: expose a stable SieveContract that uses the
  bound exported by Sieve.GallagherConservative.
-/
import Mathlib
import Sieve.LinearSieveBounds
import Sieve.GallagherConservative

noncomputable section
open Classical

namespace Sieve.GallagherHook

/-- Downstream-ready contract using the Gallagher conservative bound. -/
def contract : Sieve.LinearSieveBounds.SieveContract :=
  { gallagher := Sieve.GallagherConservative.bound }

end Sieve.GallagherHook
