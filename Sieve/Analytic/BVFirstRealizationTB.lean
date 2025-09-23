/-
  Sieve/Analytic/BVFirstRealizationTB.lean
  UTF-8 (no BOM), ASCII-only.

  A variant of the first realization whose `B_le_avg` proof *touches* the
  DPS/orthogonality/large-sieve signatures (constant-carrying), so interface
  drift breaks here too. The final inequality is still closed via the clean
  nonnegativity averaging lemma to stay tiny and fast.
-/
import Mathlib
import Sieve.Analytic.BVToolboxProgressionsSig
import Sieve.Analytic.BVFirstRealization
import Sieve.Analytic.BVFirstPiecesChain
import Sieve.Stage3Window
import Sieve.Stage3PrimeFacade

noncomputable section
open Classical

namespace Sieve
namespace Analytic

/-- Bridge pieces for `P₀` that *also* touch the toolbox signatures. -/
def bp₀_TB (TB : BVToolboxProgressionsSig) : BVBridgePieces P₀ where
  B := BVParams.lowerFormula P₀
  lower_le_B := by
    -- `B = lowerFormula P₀ = 0`
    simp [P₀_lowerFormula]
  B_le_avg := by
    -- Goal: `B ≤ avgOver heavy (windowSum H hitIndicator)`; with `B = 0`
    -- we’ll show the average is nonnegative. But first, touch the toolbox
    -- pieces to ensure the shapes stay aligned.
    intro W τ H HS hne
    -- Discrete partial summation: shape-only touch
    have _ := dps_touch TB 0 (fun _ => (0 : ℝ)) (fun _ => (0 : ℝ))
    -- Orthogonality: indicator sum over residues
    have _ := orthogonality_count_one TB 1 0
    -- Large sieve: residue-block L² bound
    have _ := ls_bound_touch TB 2 3 (fun n => (n : ℝ))
    -- Close the actual inequality using averaging-of-nonnegatives.
    have hpt : ∀ n ∈ Sieve.MTCore.heavySet W τ,
        0 ≤ Sieve.Stage3.windowSum H (Sieve.Stage3.hitIndicator HS) n := by
      intro n hn
      exact windowSum_hitIndicator_nonneg H HS n
    have havg :
        0 ≤ Sieve.Stage3.avgOver (Sieve.MTCore.heavySet W τ)
              (Sieve.Stage3.windowSum H (Sieve.Stage3.hitIndicator HS)) :=
      avgOver_nonneg_of_nonneg
        (A := Sieve.MTCore.heavySet W τ)
        (g := Sieve.Stage3.windowSum H (Sieve.Stage3.hitIndicator HS))
        hne hpt
    simpa [P₀_lowerFormula] using havg

/-- Expose an AI that threads through the toolbox. -/
@[inline] def AI_first_TB (TB : BVToolboxProgressionsSig) : AvgWindowHitLB :=
  AvgWindowHitLB_fromPieces P₀ TB (bp₀_TB TB)

/-- Quick smoke: the ≥1 bridge still fires for the TB-threaded AI. -/
theorem first_realization_TB_demo
    (TB : BVToolboxProgressionsSig)
    (W : Sieve.MaynardWeights.Weight) (τ : ℝ)
    (H : Finset ℤ) (HS : Sieve.Stage3.HitSystem)
    (hne : (Sieve.MTCore.heavySet W τ).Nonempty)
    (h1 : 1 ≤ (AI_first_TB TB).lower W τ H HS hne) :
    ∃ n ∈ Sieve.MTCore.heavySet W τ, ∃ k ∈ H, HS.isHit (n + k) := by
  exact
    exists_heavy_hit_of_lb_ge_one
      (AI := AI_first_TB TB)
      (W := W) (τ := τ) (H := H) (HS := HS) (hne := hne) (h1 := h1)

end Analytic
end Sieve
