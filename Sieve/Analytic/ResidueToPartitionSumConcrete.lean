/-
  Sieve/Analytic/ResidueToPartitionSumConcrete.lean

  Purpose
  -------
  Mirror of `PartitionSumLower` with a “concrete” record you can fill from
  DPS → orthogonality → large-sieve work. We then package it into a
  `WindowDensityLower` with δ = γ via `WindowDensityLower_ofPartitionSum`.

  No analysis is done here; it’s typed plumbing in a leaf.
-/
import Mathlib
import Sieve.Stage3
import Sieve.Stage3Window
import Sieve.Analytic.FirstMomentFromToyDensity
import Sieve.Analytic.ResidueToDensityFromSum

noncomputable section
open Classical

namespace Sieve
namespace Analytic

/-- Concrete data for the *sum-over-residues* lower-bound route. -/
structure ResidueToPartitionSumConcrete where
  q       : ℕ
  contrib :
    (W : Sieve.MaynardWeights.Weight) → (τ : ℝ) →
    (H : Finset ℤ) → (HS : Sieve.Stage3.HitSystem) →
    (n : ℤ) → ℕ → ℝ
  decompose :
    ∀ (W : Sieve.MaynardWeights.Weight) (τ : ℝ)
      (H : Finset ℤ) (HS : Sieve.Stage3.HitSystem) (n : ℤ),
      Sieve.Stage3.windowSum H (Sieve.Stage3.hitIndicator HS) n
        = ∑ r ∈ Finset.range q, contrib W τ H HS n r
  γ : ℝ
  sum_ge :
    ∀ (W : Sieve.MaynardWeights.Weight) (τ : ℝ)
      (H : Finset ℤ) (HS : Sieve.Stage3.HitSystem)
      (_hne : (Sieve.MTCore.heavySet W τ).Nonempty)
      (n : ℤ) (_hn : n ∈ Sieve.MTCore.heavySet W τ),
      γ * (H.card : ℝ) ≤ ∑ r ∈ Finset.range q, contrib W τ H HS n r

/-- Package the concrete data into the generic `PartitionSumLower`. -/
def PartitionSumLower.ofConcrete (C : ResidueToPartitionSumConcrete) : PartitionSumLower :=
{ q := C.q
, contrib := C.contrib
, decompose := C.decompose
, γ := C.γ
, sum_ge := by
    intro W τ H HS hne n hn
    exact C.sum_ge W τ H HS hne n hn
}

/-- Obtain a pointwise window-density with δ = γ from the concrete data. -/
def WindowDensityLower_ofPartitionSumConcrete (C : ResidueToPartitionSumConcrete) : WindowDensityLower :=
  WindowDensityLower_ofPartitionSum (PartitionSumLower.ofConcrete C)

/-- Smoke: keep the surface watched. -/
theorem residue_partition_sum_concrete_wired : True := by
  let _ := @PartitionSumLower.ofConcrete
  let _ := @WindowDensityLower_ofPartitionSumConcrete
  exact True.intro

end Analytic
end Sieve
