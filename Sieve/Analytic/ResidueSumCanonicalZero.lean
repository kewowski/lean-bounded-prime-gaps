/-
  Sieve/Analytic/ResidueSumCanonicalZero.lean

  Purpose
  -------
  A zero-risk builder: given ANY residue-sum decomposition
    windowSum … n = ∑_{r<q} contrib … r,
  package it as `ResidueToPartitionSumConcrete` with γ = 0.

  Why useful
  ----------
  • You can plug your *canonical* residue slice + decomposition lemma here.
  • No further analysis needed yet: `sum_ge` follows from nonnegativity of the
    window hit-sum, rewritten by `decompose`.
  • Later, upgrade γ>0 (sum lower bound) without changing shapes.

  This is leaf-only, no Stage-2/3 changes.
-/
import Mathlib
import Sieve.Stage3
import Sieve.Stage3Window
import Sieve.Analytic.ResidueToPartitionSumConcrete

noncomputable section
open Classical

namespace Sieve
namespace Analytic

/-- Local: hit-sum over any finite window is nonnegative. -/
lemma window_hit_sum_nonneg
    (H : Finset ℤ) (HS : Sieve.Stage3.HitSystem) (n : ℤ) :
    0 ≤ Sieve.Stage3.windowSum H (Sieve.Stage3.hitIndicator HS) n := by
  classical
  refine Finset.sum_nonneg ?hnonneg
  intro h hh
  by_cases hp : HS.isHit (n + h)
  · simp [Sieve.Stage3.hitIndicator, hp]    -- term = 1 ≥ 0
  · simp [Sieve.Stage3.hitIndicator, hp]    -- term = 0 ≥ 0

/--
Minimal data for a decomposition into `q` parts:
you specify the part-contribution `contrib` and the exact `decompose` identity.
-/
structure ResidueSumDecompose where
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

/--
Package any residue-sum decomposition into a concrete sum-over-residues
instance with γ = 0. The lower bound `sum_ge` is just nonnegativity of the
window hit-sum, rewritten via `decompose`.
-/
def ResidueToPartitionSumConcrete.ofZeroGamma (D : ResidueSumDecompose)
    : ResidueToPartitionSumConcrete :=
{ q := D.q
, contrib := D.contrib
, decompose := D.decompose
, γ := 0
, sum_ge := by
    intro W τ H HS _hne n _hn
    -- 0 ≤ RHS by nonnegativity, after rewriting with the decomposition.
    simpa [D.decompose W τ H HS n] using window_hit_sum_nonneg H HS n
}

/-- Smoke: keep the surface watched. -/
theorem residue_sum_canonical_zero_wired : True := by
  let _ := @ResidueToPartitionSumConcrete.ofZeroGamma
  exact True.intro

end Analytic
end Sieve
