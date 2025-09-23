/-
  Sieve/Analytic/BVMainTheoremSpec.lean
  UTF-8 (no BOM), ASCII-only.

  A concrete, *constant-carrying* statement name for the BV/EH lower bound target.
  This is the single inequality future analytic work should aim to prove. It is
  intentionally just a `Prop` (no proofs here), and is definitionally the same
  as `BVMainStatement` so downstream code can use either name.

  Usage:
  - State/assume `h : BVMainTheoremSpec P TB`.
  - Turn it into an analytic provider with `AI_of_BVSpec P TB h`.
  - Feed that `AvgWindowHitLB` into the Stage-3 wrappers (≥1 / ≥2).

  Notes:
  - `P : BVParams` carries constants (`θ, k, Cmain, Cerr, x0`) and sign witnesses.
  - `TB : BVToolbox` holds the named analytic tools (large sieve, orthogonality, etc.).
-/
import Mathlib
import Sieve.Analytic.BVMainStatement

noncomputable section
open Classical

namespace Sieve
namespace Analytic

/-- The BV/EH *main theorem specification*: a constant-carrying inequality that
matches the Stage-3 average functional. This is the target to prove analytically. -/
def BVMainTheoremSpec (P : BVParams) (TB : BVToolbox) : Prop :=
  BVMainStatement P TB

@[simp] theorem BVMainTheoremSpec_iff (P : BVParams) (TB : BVToolbox) :
  BVMainTheoremSpec P TB ↔ BVMainStatement P TB := Iff.rfl

/-- Build an `AvgWindowHitLB` from any proof of `BVMainTheoremSpec`. -/
def AI_of_BVSpec (P : BVParams) (TB : BVToolbox)
    (h : BVMainTheoremSpec P TB) : AvgWindowHitLB :=
  AI_of_BV P TB (by simpa [BVMainTheoremSpec_iff] using h)

end Analytic
end Sieve
