/-
  Sieve/Analytic/ResidueSumToy.lean

  Toy realized instance of the *sum-over-residues* route with q = 1.
  We define `contrib` to be the entire window sum (ignoring r), so the
  decomposition is tautological, and we take γ = 0 so `sum_ge` is just
  nonnegativity of the window-hit sum.

  This file is to exercise the concrete route; later swap `contrib`/γ
  for a true residue slice and a positive γ from DPS/orthogonality/LS.
-/
import Mathlib
import Sieve.Stage3
import Sieve.Stage3Window
import Sieve.Stage3PrimeFacade
import Sieve.Analytic.ResidueToPartitionSumConcrete

noncomputable section
open Classical

namespace Sieve
namespace Analytic

/-- Local: window hit-sum over any finite window is nonnegative. -/
lemma window_hit_sum_nonneg
    (H : Finset ℤ) (HS : Sieve.Stage3.HitSystem) (n : ℤ) :
    0 ≤ Sieve.Stage3.windowSum H (Sieve.Stage3.hitIndicator HS) n := by
  classical
  refine Finset.sum_nonneg ?hnonneg
  intro h hh
  by_cases hp : HS.isHit (n + h)
  · simp [Sieve.Stage3.hitIndicator, hp]   -- term = 1 ≥ 0
  · simp [Sieve.Stage3.hitIndicator, hp]   -- term = 0 ≥ 0

/-- The toy contribution ignores `r` and is just the whole window sum. -/
def toyContrib :
    (W : Sieve.MaynardWeights.Weight) → (τ : ℝ) →
    (H : Finset ℤ) → (HS : Sieve.Stage3.HitSystem) →
    (n : ℤ) → ℕ → ℝ :=
  fun _W _τ H HS n _r => Sieve.Stage3.windowSum H (Sieve.Stage3.hitIndicator HS) n

/-- A toy concrete instance for the sum-over-residues route with q = 1. -/
def ToyResidueSumConcrete : ResidueToPartitionSumConcrete :=
{ q := 1
, contrib := toyContrib
, decompose := by
    intro W τ H HS n
    -- ∑_{r∈range 1} constant = constant
    simp [toyContrib, Finset.range_one]
, γ := 0
, sum_ge := by
    intro W τ H HS _hne n _hn
    -- 0 ≤ ∑ contrib = windowSum …
    simpa [toyContrib, Finset.range_one] using
      (window_hit_sum_nonneg H HS n)
}

/-- For convenience: the ready window-density from the toy instance (δ = 0). -/
def ToyResidueSumDensity : WindowDensityLower :=
  WindowDensityLower_ofPartitionSumConcrete ToyResidueSumConcrete

/-- Smoke: everything wires up. -/
theorem toy_residue_sum_wired : True := by
  let _ := ToyResidueSumConcrete
  let _ := ToyResidueSumDensity
  exact True.intro

end Analytic
end Sieve
