/-
  Sieve/Analytic/ResidueToDensityFromSum.lean

  Bridge: if you can prove a *sum-over-residues* lower bound
    ∑_{r<q} contrib(r) ≥ γ · |H|
  together with the exact decomposition
    windowSum … n = ∑_{r<q} contrib(r),
  then you get a pointwise window-density with δ = γ.

  This complements the PartitionBetaLower route by avoiding per-residue β_r.
-/
import Mathlib
import Sieve.Stage3
import Sieve.Stage3Window
import Sieve.Analytic.FirstMomentFromToyDensity  -- for WindowDensityLower

noncomputable section
open Classical

namespace Sieve
namespace Analytic

/-- Data for a *sum* lower bound across a residue-style partition. -/
structure PartitionSumLower where
  q       : ℕ
  /-- Contribution of part `r` at point `n`. -/
  contrib :
    (W : Sieve.MaynardWeights.Weight) → (τ : ℝ) →
    (H : Finset ℤ) → (HS : Sieve.Stage3.HitSystem) →
    (n : ℤ) → ℕ → ℝ
  /-- Exact decomposition of the window sum. -/
  decompose :
    ∀ (W : Sieve.MaynardWeights.Weight) (τ : ℝ)
      (H : Finset ℤ) (HS : Sieve.Stage3.HitSystem) (n : ℤ),
      Sieve.Stage3.windowSum H (Sieve.Stage3.hitIndicator HS) n
        = ∑ r ∈ Finset.range q, contrib W τ H HS n r
  /-- The global constant `γ` for the sum lower bound. -/
  γ : ℝ
  /-- Pointwise (on the heavy set): total contrib across `r<q` is ≥ γ · |H|. -/
  sum_ge :
    ∀ (W : Sieve.MaynardWeights.Weight) (τ : ℝ)
      (H : Finset ℤ) (HS : Sieve.Stage3.HitSystem)
      (_hne : (Sieve.MTCore.heavySet W τ).Nonempty)
      (n : ℤ) (_hn : n ∈ Sieve.MTCore.heavySet W τ),
      γ * (H.card : ℝ) ≤ ∑ r ∈ Finset.range q, contrib W τ H HS n r

/-- From a sum-over-residues lower bound, produce a pointwise window-density with δ = γ. -/
def WindowDensityLower_ofPartitionSum (P : PartitionSumLower) : WindowDensityLower :=
{ δ := P.γ
, pointwise := by
    intro W τ H HS hne n hn
    -- `sum_ge` is exactly the desired bound, and `decompose` identifies the RHS as the window sum.
    simpa [P.decompose W τ H HS n] using
      (P.sum_ge W τ H HS hne n hn)
}

/-- Smoke: keep the surface watched by the compiler. -/
theorem partition_sum_to_density_wired : True := by
  let _ := @WindowDensityLower_ofPartitionSum
  exact True.intro

end Analytic
end Sieve
