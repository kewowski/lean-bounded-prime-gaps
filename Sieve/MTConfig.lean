/-
  Sieve/MTConfig.lean
  UTF-8 (no BOM), ASCII-only.
-/
import Mathlib
import Sieve.GallagherHook
import Sieve.Pipeline
import Sieve.Examples

noncomputable section
open Classical

namespace Sieve.MTConfig

/-- Default, always-green MT config:
    - conservative Gallagher contract (via the hook)
    - trivial admissible tuple `{0}` from `Sieve.Examples` -/
def default : Sieve.Pipeline.Config :=
  { chars      := by exact Character.decomp_available
    contract   := Sieve.GallagherHook.contract
    tuple      := ({0} : Finset ℤ)
    admissible := Sieve.Examples.admissible_singleton 0 }

end Sieve.MTConfig
