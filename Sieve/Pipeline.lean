/-
  Sieve/Pipeline.lean
  UTF-8 (no BOM), ASCII-only.
-/
import Mathlib
import Character.Decompositions
import Sieve.AdmissibleTuples
import Sieve.MaynardWeights
import Sieve.LinearSieveBounds
import Sieve.MTMoments   -- new

noncomputable section
open Classical

namespace Sieve.Pipeline

/-- Minimal record for a configured sieve pipeline. -/
structure Config where
  chars      : Character.DecompositionAvailable := Character.decomp_available
  contract   : Sieve.LinearSieveBounds.SieveContract
  tuple      : Finset ℤ
  admissible : Sieve.AdmissibleTuples.Admissible tuple

/-- Stage 1: package a provided weight and attach basic moment values
    (lower/upper bounds set to the computed moments for now). -/
def stage1 (_P : Config) (W : Sieve.MaynardWeights.Weight)
  : Sieve.MaynardWeights.BuiltWeight :=
  let m1 := Sieve.MTMoments.firstMoment W
  let m2 := Sieve.MTMoments.secondMoment W
  { base := W
    hits := { firstMomentLower := m1
              secondMomentUpper := m2
              dispersionUpper := 0 } }

end Sieve.Pipeline
