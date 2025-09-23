/-
  Sieve/Analytic/BVFirstRealization.lean
  UTF-8 (no BOM), ASCII-only.
-/
import Mathlib
import Sieve.Analytic.Constants
import Sieve.Analytic.BVMainDeriveFromToolbox
import Sieve.Analytic.BVToolboxProgressionsSig
import Sieve.Stage3Window
import Sieve.Stage3PrimeFacade

noncomputable section
open Classical

namespace Sieve
namespace Analytic

def P₀ : BVParams where
  N := 2
  hN2 := by decide
  Cmain := 0
  Cerr1 := 0
  Cerr2 := 0
  threshold := 0
  logN_pos := by
    have h0  : (0 : ℝ) ≤ (2 : ℝ) := by norm_num
    have h12 : (1 : ℝ) <  (2 : ℝ) := by norm_num
    have hiff : 0 < Real.log (2 : ℝ) ↔ 1 < (2 : ℝ) :=
      Real.log_pos_iff (x := (2 : ℝ)) h0
    exact hiff.mpr h12

@[simp] lemma P₀_lowerFormula : BVParams.lowerFormula P₀ = 0 := by
  simp [BVParams.lowerFormula, BVParams.logN, P₀]

@[simp] lemma hitIndicator_nonneg
    (HS : Sieve.Stage3.HitSystem) (m : ℤ) :
    0 ≤ Sieve.Stage3.hitIndicator HS m := by
  classical
  by_cases p : Sieve.Stage3.HitSystem.isHit HS m
  all_goals
    simp [Sieve.Stage3.hitIndicator, p]

lemma windowSum_hitIndicator_nonneg
    (H : Finset ℤ) (HS : Sieve.Stage3.HitSystem) (n : ℤ) :
    0 ≤ Sieve.Stage3.windowSum H (Sieve.Stage3.hitIndicator HS) n := by
  classical
  have hterm : ∀ h ∈ H, 0 ≤ (Sieve.Stage3.hitIndicator HS) (n + h) := by
    intro h hh; exact hitIndicator_nonneg HS (n + h)
  have hsum : 0 ≤ ∑ h ∈ H, (Sieve.Stage3.hitIndicator HS) (n + h) :=
    Finset.sum_nonneg (by intro h hh; exact hterm h hh)
  change 0 ≤ ∑ h ∈ H, (Sieve.Stage3.hitIndicator HS) (n + h)
  exact hsum

lemma avgOver_nonneg_of_nonneg
    (A : Finset ℤ) (g : ℤ → ℝ) (hA : A.Nonempty)
    (hg : ∀ n ∈ A, 0 ≤ g n) :
    0 ≤ Sieve.Stage3.avgOver A g := by
  classical
  have hsum : 0 ≤ ∑ n ∈ A, g n :=
    Finset.sum_nonneg (by intro n hn; exact hg n hn)
  have hpos : 0 < (A.card : ℝ) := by
    exact_mod_cast (Finset.card_pos.mpr hA)
  have hden : 0 ≤ (A.card : ℝ) := le_of_lt hpos
  change 0 ≤ (∑ n ∈ A, g n) / (A.card : ℝ)
  exact div_nonneg hsum hden

def bp₀ : BVBridgePieces P₀ where
  B := BVParams.lowerFormula P₀
  lower_le_B := by
    simp [P₀_lowerFormula]
  B_le_avg := by
    intro W τ H HS hne
    have hpt : ∀ n ∈ Sieve.MTCore.heavySet W τ,
        0 ≤ Sieve.Stage3.windowSum H (Sieve.Stage3.hitIndicator HS) n := by
      intro n hn; exact windowSum_hitIndicator_nonneg H HS n
    have h :=
      avgOver_nonneg_of_nonneg
        (A := Sieve.MTCore.heavySet W τ)
        (g := Sieve.Stage3.windowSum H (Sieve.Stage3.hitIndicator HS))
        hne hpt
    simp [P₀_lowerFormula] at h ⊢
    exact h

@[inline] def AI_first (TB : BVToolboxProgressionsSig) : AvgWindowHitLB :=
  AvgWindowHitLB_fromPieces P₀ TB bp₀

end Analytic
end Sieve
