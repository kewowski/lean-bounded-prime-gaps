/-
  Sieve/Analytic/BVToolboxAPI.lean
  UTF-8 (no BOM), ASCII-only.

  Purpose
  -------
  A minimal, signatures-only API that ties a (future) BV/EH toolbox to the
  single-gateway inequality `BVMainIneq P`, and then packages it as the
  Stage-3 analytic interface `AvgWindowHitLB`.

  • No proofs here; implementers will supply `derive : BVMainIneq P`.
  • Keeps Stage-2/3 unchanged while giving downstream a stable handle.
-/
import Mathlib
import Sieve.Analytic.BVToolboxProgressionsSig
import Sieve.Analytic.BVMainIneq
import Sieve.Analytic.BVMainRealize

noncomputable section

namespace Sieve
namespace Analytic

/--
API bundle for Bombieri–Vinogradov/Elliott–Halberstam style inputs
targeted at a fixed parameter pack `P : BVParams`.

* `TB` holds signatures for core progression-analytic tools (shapes only).
* `derive` is the single inequality `BVMainIneq P` that Stage-3 consumes.
-/
structure BVToolboxAPI (P : BVParams) where
  TB     : BVToolboxProgressionsSig
  derive : BVMainIneq P

/-- Package the provided inequality into the Stage-3 analytic interface. -/
def AvgWindowHitLB_of (P : BVParams) (api : BVToolboxAPI P) : AvgWindowHitLB :=
  AI_of_BV_ofIneq P api.derive

end Analytic
end Sieve
