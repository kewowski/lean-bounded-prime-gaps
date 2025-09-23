/-
  Sieve/Analytic/ResidueToPartitionConcrete.lean

  Purpose
  -------
  A leaf-only skeleton: you supply a concrete residue decomposition and
  per-residue lower bounds; we package it as `PartitionBetaLower` and then
  as a ready `WindowDensityLower` via `WindowDensityLower_ofPartition`.

  How to use
  ----------
  • Instantiate `ResidueToPartitionConcrete` with:
      - `q`         : your modulus,
      - `β`         : per-residue constants,
      - `contrib`   : residue-`r` contribution at point `n`,
      - `decompose` : identity writing `windowSum … n = ∑_{r<q} contrib … r`,
      - `contrib_ge`: pointwise bound `β r · |H| ≤ contrib … r` on the heavy set.
  • Then call `WindowDensityLower_ofResiduePartition C` to get a
    `WindowDensityLower` with `δ = ∑_{r<q} β r`.

  Notes
  -----
  • No analysis is done here; all heavy lifting happens in the data you provide.
  • Shapes match Stage-3 binders exactly, so downstream stays unchanged.
-/
import Mathlib
import Sieve.Stage3
import Sieve.Stage3Window
import Sieve.Analytic.FirstMomentFromToyDensity
import Sieve.Analytic.ResidueToDensityFromPartition

noncomputable section
open Classical

namespace Sieve
namespace Analytic

/-- Concrete residue partition data you provide. -/
structure ResidueToPartitionConcrete where
  q       : ℕ
  β       : ℕ → ℝ
  contrib :
    (W : Sieve.MaynardWeights.Weight) → (τ : ℝ) →
    (H : Finset ℤ) → (HS : Sieve.Stage3.HitSystem) →
    (n : ℤ) → ℕ → ℝ
  /-- Exact decomposition: `windowSum … n = ∑_{r<q} contrib … r`. -/
  decompose :
    ∀ (W : Sieve.MaynardWeights.Weight) (τ : ℝ)
      (H : Finset ℤ) (HS : Sieve.Stage3.HitSystem) (n : ℤ),
      Sieve.Stage3.windowSum H (Sieve.Stage3.hitIndicator HS) n
        = ∑ r ∈ Finset.range q, contrib W τ H HS n r
  /-- Pointwise per-residue bound on the heavy set. -/
  contrib_ge :
    ∀ (W : Sieve.MaynardWeights.Weight) (τ : ℝ)
      (H : Finset ℤ) (HS : Sieve.Stage3.HitSystem)
      (_hne : (Sieve.MTCore.heavySet W τ).Nonempty)
      (n : ℤ) (_hn : n ∈ Sieve.MTCore.heavySet W τ)
      (r : ℕ), r ∈ Finset.range q →
      β r * (H.card : ℝ) ≤ contrib W τ H HS n r

/-- Turn concrete residue data into the generic partition record. -/
def PartitionBetaLower.ofConcrete (C : ResidueToPartitionConcrete) : PartitionBetaLower :=
{ q        := C.q
, β        := C.β
, contrib  := C.contrib
, decompose := C.decompose
, contrib_ge := by
    intro W τ H HS hne n hn r hr
    exact C.contrib_ge W τ H HS hne n hn r hr
}

/-- From concrete residue data, obtain a ready pointwise window-density. -/
def WindowDensityLower_ofResiduePartition (C : ResidueToPartitionConcrete) : WindowDensityLower :=
  WindowDensityLower_ofPartition (PartitionBetaLower.ofConcrete C)

/-- Smoke: keep the surface watched by the compiler. -/
theorem residue_partition_concrete_wired : True := by
  let _ := @PartitionBetaLower.ofConcrete
  let _ := @WindowDensityLower_ofResiduePartition
  exact True.intro

end Analytic
end Sieve
