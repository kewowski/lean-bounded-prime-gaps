/-
  Sieve/Analytic/ResidueSumCanonicalQ1.lean

  Canonical residue slice realization for q = 1.
  Decomposition is tautological because h % 1 = 0 for all integers h.
  We package it via `ResidueToPartitionSumConcrete.ofZeroGamma` (γ = 0).
-/
import Mathlib
import Sieve.Stage3
import Sieve.Stage3Window
import Sieve.Analytic.ResidueSliceCanonical
import Sieve.Analytic.ResidueSumCanonicalZero
import Sieve.Analytic.ResidueToPartitionSumConcrete
import Sieve.Analytic.ResidueToDensityFromSum

noncomputable section
open Classical

namespace Sieve
namespace Analytic

/-- The q=1 canonical residue-sum decomposition data. -/
def CanonicalQ1_Decompose : ResidueSumDecompose :=
{ q := 1
, contrib := fun _W _τ H HS n r =>
    -- canonical slice at residue r (here only r=0 exists)
    canonicalResidueContrib 1 _W _τ H HS n r
, decompose := by
    intro W τ H HS n
    -- windowSum = ∑_{r<1} contrib … = contrib … 0
    -- and H.filter (fun h => h % 1 = 0) = H
    simp [canonicalResidueContrib, Finset.range_one, Sieve.Stage3.windowSum]
}

/-- Concrete γ-route instance for q=1 with γ=0 (nonnegativity only). -/
def CanonicalQ1_Concrete : ResidueToPartitionSumConcrete :=
  ResidueToPartitionSumConcrete.ofZeroGamma CanonicalQ1_Decompose

/-- The resulting window-density (δ = γ = 0). -/
def CanonicalQ1_Density : WindowDensityLower :=
  WindowDensityLower_ofPartitionSumConcrete CanonicalQ1_Concrete

/-- Smoke: keep surface watched. -/
theorem canonical_q1_wired : True := by
  let _ := CanonicalQ1_Decompose
  let _ := CanonicalQ1_Concrete
  let _ := CanonicalQ1_Density
  exact True.intro

end Analytic
end Sieve
