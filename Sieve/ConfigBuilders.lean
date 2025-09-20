/-
  Sieve/ConfigBuilders.lean
  Convenience constructors for `Pipeline.Config`:
  - conservative (B = 0)
  - simple non-zero Gallagher with a chosen window and abs-cap
-/
import Mathlib
import Sieve.Pipeline
import Sieve.GallagherHook
import Sieve.GallagherSimple

noncomputable section
open Classical

namespace Sieve.ConfigBuilders

/-- Build a conservative config (B = 0) for a given tuple + admissibility proof. -/
def conservative
    (tuple : Finset ℤ) (adm : Sieve.AdmissibleTuples.Admissible tuple)
    : Sieve.Pipeline.Config :=
{ chars      := Character.decomp_available
, contract   := Sieve.GallagherHook.contract
, tuple      := tuple
, admissible := adm }

/-- Build a simple non-zero Gallagher config from a window `S` and abs-cap `Mabs`
    for a given tuple + admissibility proof. -/
def simple
    (S : Finset ℤ) (Mabs : ℝ)
    (tuple : Finset ℤ) (adm : Sieve.AdmissibleTuples.Admissible tuple)
    : Sieve.Pipeline.Config :=
{ chars      := Character.decomp_available
, contract   := Sieve.GallagherSimple.contract_of_absWindow S Mabs
, tuple      := tuple
, admissible := adm }

end Sieve.ConfigBuilders
