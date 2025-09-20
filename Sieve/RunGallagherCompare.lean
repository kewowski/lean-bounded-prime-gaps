/-
  Sieve/RunGallagherCompare.lean
  Compare conservative vs simple Gallagher B on a symmetric integer window S = [-M, M].
-/
import Mathlib
import Sieve.AdmissibleTwin
import Sieve.GallagherHook        -- conservative contract
import Sieve.GallagherSimple      -- simple non-zero contract
import Sieve.Pipeline
import Sieve.Stage2

noncomputable section
open Classical

namespace Sieve.RunGallagherCompare
open Sieve.Stage2

/-- Symmetric integer window `[-M, M]` as a Finset. We take `M : ℕ` for clarity. -/
def symmWindow (M : ℕ) : Finset ℤ :=
  Finset.Icc (-(Int.ofNat M)) (Int.ofNat M)

/-- Twin config with the *conservative* (B = 0) contract. -/
def twinConfig_conservative : Sieve.Pipeline.Config :=
{ chars      := Character.decomp_available
, contract   := Sieve.GallagherHook.contract
, tuple      := Sieve.AdmissibleTwin.twin
, admissible := Sieve.AdmissibleTwin.admissible_twin }

/-- Twin config with the *simple* (non-zero) contract using window `[-M,M]`
    and a uniform absolute bound `Mabs` for the relevant sum terms. -/
def twinConfig_simple (M : ℕ) (Mabs : ℝ) : Sieve.Pipeline.Config :=
{ chars      := Character.decomp_available
, contract   := Sieve.GallagherSimple.contract_of_absWindow (symmWindow M) Mabs
, tuple      := Sieve.AdmissibleTwin.twin
, admissible := Sieve.AdmissibleTwin.admissible_twin }

/-- Sanity checks: both Bs are nonnegative (conservative is exactly 0). -/
example : 0 ≤ (run twinConfig_conservative).B :=
  (run twinConfig_conservative).nonneg

example (M : ℕ) (Mabs : ℝ) : 0 ≤ (run (twinConfig_simple M Mabs)).B :=
  (run (twinConfig_simple M Mabs)).nonneg

/-- If you ever need to *inspect* the simple B: it is by definition `(card S)^2 * Mabs^2`. -/
example (M : ℕ) (Mabs : ℝ) :
    (run (twinConfig_simple M Mabs)).B
      = ( (symmWindow M).card : ℝ )^2 * Mabs^2 := rfl

end Sieve.RunGallagherCompare
