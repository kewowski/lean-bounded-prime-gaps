/-
  Sieve/Analytic/BVToolboxOrthoOnly.lean
  UTF-8 (no BOM), ASCII-only.

  Purpose:
  Provide a tiny helper to assemble a `BVToolbox` when you already have:
    • a `LargeSieveProgressions` record `ls`
    • a `PartialSummationBound` record `ps`
  We fill in the orthogonality field using our proven constructor
  `mkOrthogonalityIdentity` (q ≥ 1 ⇒ ∑_n 1_{n≡r} = 1).

  This keeps the bridge code small and green while we work on the remaining
  large-sieve / partial-summation pieces separately.
-/
import Mathlib
import Sieve.Analytic.BVToolboxSpec
import Sieve.Analytic.OrthogonalityIdentityImpl

noncomputable section
open Classical

namespace Sieve
namespace Analytic

/--
Build a full `BVToolbox` by supplying `ls` (large-sieve spec) and `ps` (partial
summation bound). The orthogonality identity is constructed canonically from `ls.q`.
-/
def mkBVToolboxWithOrtho (ls : LargeSieveProgressions) (ps : PartialSummationBound) : BVToolbox :=
{ ls := ls
, ortho := mkOrthogonalityIdentity ls.q ls.hq_pos
, ps := ps
}

end Analytic
end Sieve
