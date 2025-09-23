/-
  Sieve/Analytic/RunAIFromResidueSmoke.lean
-/
import Mathlib
import Sieve.Analytic.AIFromResidue
import Sieve.AnalyticBridge
import Sieve.Stage3PrimeFacade

noncomputable section
open Classical

namespace Sieve
namespace Analytic

lemma windowSum_nonneg
    (H : Finset ℤ) (HS : Stage3.HitSystem) (n : ℤ) :
    0 ≤ Stage3.windowSum H (Stage3.hitIndicator HS) n := by
  classical
  have hterm :
      ∀ h ∈ H, 0 ≤ (if HS.isHit (n + h) then (1 : ℝ) else 0) := by
    intro h hh; by_cases p : HS.isHit (n + h) <;> simp [p]
  have hsum :
      0 ≤ ∑ h ∈ H, (if HS.isHit (n + h) then (1 : ℝ) else 0) :=
    Finset.sum_nonneg hterm
  change 0 ≤ ∑ h ∈ H, (if HS.isHit (n + h) then (1 : ℝ) else 0)
  exact hsum

def ResidueLBSpec.zero : ResidueLBSpec where
  δ := 0
  per_point := by
    intro W τ H HS _hne n _hn
    have h := windowSum_nonneg H HS n
    rw [zero_mul]
    exact h

@[inline] def AI_residue_zero : AvgWindowHitLB :=
  AI_fromResidue (ResidueLBSpec.zero)

theorem residue_zero_bridge_smoke
    (W : Sieve.MaynardWeights.Weight) (τ : ℝ)
    (H : Finset ℤ) (HS : Stage3.HitSystem)
    (hne : (MTCore.heavySet W τ).Nonempty)
    (h1  : 1 ≤ (AI_residue_zero).lower W τ H HS hne) :
    ∃ n ∈ MTCore.heavySet W τ, ∃ k ∈ H, HS.isHit (n + k) := by
  exact
    exists_heavy_hit_of_lb_ge_one
      (AI := AI_residue_zero)
      (W := W) (τ := τ) (H := H) (HS := HS) (hne := hne) (h1 := h1)

theorem residue_ai_compiles : True := by
  let _AI : AvgWindowHitLB := AI_residue_zero
  exact True.intro

end Analytic
end Sieve
