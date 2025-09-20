/-
  Sieve/RunConfigBuildersDemo.lean
  Demo: build configs via helpers (conservative & simple) and check B ≥ 0.
-/
import Mathlib
import Sieve.ConfigBuilders
import Sieve.AdmissibleTwin
import Sieve.Pipeline
import Sieve.Stage2

noncomputable section
open Classical

namespace Sieve.RunConfigBuildersDemo

/-- Symmetric integer window `[-M, M]`. -/
def window (M : ℕ) : Finset ℤ :=
  Finset.Icc (-(Int.ofNat M)) (Int.ofNat M)

/-- Conservative config for twins. -/
def cfgCons : Sieve.Pipeline.Config :=
  Sieve.ConfigBuilders.conservative
    Sieve.AdmissibleTwin.twin
    Sieve.AdmissibleTwin.admissible_twin

/-- Simple (non-zero) Gallagher config for twins with window `[-M,M]` and cap `Mabs`. -/
def cfgSimple (M : ℕ) (Mabs : ℝ) : Sieve.Pipeline.Config :=
  Sieve.ConfigBuilders.simple
    (window M) Mabs
    Sieve.AdmissibleTwin.twin
    Sieve.AdmissibleTwin.admissible_twin

/-- Sanity: conservative `B` is nonnegative. -/
example : 0 ≤ (Sieve.Stage2.run cfgCons).B :=
  (Sieve.Stage2.run cfgCons).nonneg

/-- Sanity: simple `B` is nonnegative. -/
example (M : ℕ) (Mabs : ℝ) : 0 ≤ (Sieve.Stage2.run (cfgSimple M Mabs)).B :=
  (Sieve.Stage2.run (cfgSimple M Mabs)).nonneg

end Sieve.RunConfigBuildersDemo
