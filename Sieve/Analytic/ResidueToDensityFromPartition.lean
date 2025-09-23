/-
  Sieve/Analytic/ResidueToDensityFromPartition.lean

  General bridge:
  If you can decompose the window sum at a point `n` into `q` non-overlapping
  "parts" (e.g., residue classes) with per-part lower bounds of the form
  `β r * |H|`, then the total window sum is ≥ (∑ β r) * |H|. This gives a
  pointwise window-density with δ = ∑ β r.

  This module is purely algebraic (leaf-only), no heavy analysis.
-/
import Mathlib
import Sieve.Stage3
import Sieve.Stage3Window
import Sieve.Analytic.FirstMomentFromToyDensity  -- for WindowDensityLower

noncomputable section
open Classical

namespace Sieve
namespace Analytic

/-- Data for a partition-style lower bound:
    `windowSum H (hitIndicator HS) n` is decomposed as a sum over `r : 0..q-1`
    of contributions `contrib … r`, each bounded below by `β r * |H|`.
    The β's do **not** depend on `H`, so the total lower is `(∑ β r) * |H|`. -/
structure PartitionBetaLower where
  q       : ℕ
  β       : ℕ → ℝ
  /-- Contribution of part `r` at the point `n`. (E.g., residue-`r` slice.) -/
  contrib :
    (W : Sieve.MaynardWeights.Weight) → (τ : ℝ) →
    (H : Finset ℤ) → (HS : Sieve.Stage3.HitSystem) →
    (n : ℤ) → ℕ → ℝ
  /-- Exact decomposition of the window sum into `q` parts. -/
  decompose :
    ∀ (W : Sieve.MaynardWeights.Weight) (τ : ℝ)
      (H : Finset ℤ) (HS : Sieve.Stage3.HitSystem) (n : ℤ),
      Sieve.Stage3.windowSum H (Sieve.Stage3.hitIndicator HS) n
        = ∑ r ∈ Finset.range q, contrib W τ H HS n r
  /-- Per-part lower bound of the form `β r * |H|`. (Binder shape matches Stage-3.) -/
  contrib_ge :
    ∀ (W : Sieve.MaynardWeights.Weight) (τ : ℝ)
      (H : Finset ℤ) (HS : Sieve.Stage3.HitSystem)
      (_hne : (Sieve.MTCore.heavySet W τ).Nonempty)
      (n : ℤ) (_hn : n ∈ Sieve.MTCore.heavySet W τ)
      (r : ℕ),
      r ∈ Finset.range q →
      β r * (H.card : ℝ) ≤ contrib W τ H HS n r

/-- From a partition-style lower bound with `β r * |H|` on each part,
    get a pointwise window-density lower bound with
    `δ = ∑_{r=0}^{q-1} β r`. -/
def WindowDensityLower_ofPartition (P : PartitionBetaLower) : WindowDensityLower :=
{ δ := ∑ r ∈ Finset.range P.q, P.β r
, pointwise := by
    intro W τ H HS hne n hn
    -- Sum the per-part lower bounds over r ∈ [0..q).
    have hsum :
        (∑ r ∈ Finset.range P.q, P.β r * (H.card : ℝ))
          ≤ ∑ r ∈ Finset.range P.q, P.contrib W τ H HS n r :=
      Finset.sum_le_sum (by
        intro r hr
        exact P.contrib_ge W τ H HS hne n hn r hr)

    -- Algebra:  ∑ (β r * |H|) = (∑ β r) * |H|
    have hswap :
        (∑ r ∈ Finset.range P.q, P.β r * (H.card : ℝ))
          = (∑ r ∈ Finset.range P.q, (H.card : ℝ) * P.β r) := by
      refine Finset.sum_congr rfl ?_
      intro r _hr; simp [mul_comm]

    have hfactor :
        (∑ r ∈ Finset.range P.q, (H.card : ℝ) * P.β r)
          = (H.card : ℝ) * (∑ r ∈ Finset.range P.q, P.β r) := by
      -- `Finset.mul_sum` gives `c * ∑ = ∑ (c * ·)`; use `.symm` for our direction.
      simpa using
        (Finset.mul_sum (s := Finset.range P.q) (f := fun r => P.β r) (H.card : ℝ)).symm

    have hleft :
        (∑ r ∈ Finset.range P.q, P.β r * (H.card : ℝ))
          = (∑ r ∈ Finset.range P.q, P.β r) * (H.card : ℝ) := by
      -- Combine `hswap` and `hfactor`, then commute the scalar to the right.
      simpa [mul_comm] using (hswap.trans hfactor)

    -- Replace RHS by the decomposed window-sum and LHS by `(∑ β) * |H|`.
    have : (∑ r ∈ Finset.range P.q, P.β r) * (H.card : ℝ)
            ≤ Sieve.Stage3.windowSum H (Sieve.Stage3.hitIndicator HS) n := by
      simpa [hleft, P.decompose W τ H HS n] using hsum

    exact this
}

/-- Smoke: symbolically touch to catch signature drift. -/
theorem residue_partition_to_density_wired : True := by
  let _ := @WindowDensityLower_ofPartition
  exact True.intro

end Analytic
end Sieve
