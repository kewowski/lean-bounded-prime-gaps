/-
  Sieve/Params.lean
  UTF-8 (no BOM), ASCII-only.

  Minimal parameter bundle for Maynard–Tao style setups.
-/
import Mathlib
import Sieve.AdmissibleTuples

noncomputable section
open Classical

namespace Sieve.Params

/-- Minimal MT parameter pack: tuple `H`, its admissibility proof,
    sieve `k`, a level parameter `R`, and a working window of `n` values. -/
structure MTParams where
  H       : Finset ℤ
  H_adm   : Sieve.AdmissibleTuples.Admissible H
  k       : ℕ
  hk      : 0 < k
  R       : ℝ
  hR      : 1 ≤ R
  window  : Finset Int

end Sieve.Params
