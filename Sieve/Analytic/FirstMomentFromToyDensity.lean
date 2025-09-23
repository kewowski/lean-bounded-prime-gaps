/-
  Sieve/Analytic/FirstMomentFromToyDensity.lean

  Turn a *pointwise* window-density lower bound into a *first-moment* bound,
  then into a ready-to-use `FirstMomentVar`.

  Assumption: for every heavy n, its window sum is ≥ δ · |H|.
  Consequence: sum over heavy ≥ (|heavy|) · (δ · |H|).
-/
import Mathlib
import Sieve.Stage3
import Sieve.Stage3Window
import Sieve.Analytic.FirstMomentVar

noncomputable section
open Classical

namespace Sieve
namespace Analytic

/-- A simple per-instance window density assumption:
    every heavy point sees at least a δ-fraction of hits in its window. -/
structure WindowDensityLower where
  δ : ℝ
  /-- Pointwise lower bound: for each heavy `n`,
      the window sum is at least `δ * |H|`. -/
  pointwise :
    ∀ (W : Sieve.MaynardWeights.Weight) (τ : ℝ)
      (H : Finset ℤ) (HS : Sieve.Stage3.HitSystem)
      (_hne : (Sieve.MTCore.heavySet W τ).Nonempty)
      (n : ℤ) (_hn : n ∈ Sieve.MTCore.heavySet W τ),
      δ * (H.card : ℝ)
        ≤ Sieve.Stage3.windowSum H (Sieve.Stage3.hitIndicator HS) n

/-- Package a `WindowDensityLower` into a `FirstMomentVar`
    with `c(W,τ,H,HS,hne) = δ · |H|`. -/
def FirstMomentVar_ofDensity (D : WindowDensityLower) : FirstMomentVar :=
{ c := fun _W _τ H _HS _hne => D.δ * (H.card : ℝ)
, sum_ge := by
    intro W τ H HS hne
    -- Sum the pointwise lower bound over the heavy set.
    have hpt :
        ∀ n ∈ Sieve.MTCore.heavySet W τ,
          D.δ * (H.card : ℝ)
            ≤ Sieve.Stage3.windowSum H (Sieve.Stage3.hitIndicator HS) n := by
      intro n hn
      exact D.pointwise W τ H HS hne n hn
    have hsum :
        (∑ n ∈ Sieve.MTCore.heavySet W τ, D.δ * (H.card : ℝ))
          ≤ ∑ n ∈ Sieve.MTCore.heavySet W τ,
                Sieve.Stage3.windowSum H (Sieve.Stage3.hitIndicator HS) n :=
      Finset.sum_le_sum (by intro n hn; exact hpt n hn)
    -- Evaluate the constant sum on the left.
    have hleft :
        (∑ _n ∈ Sieve.MTCore.heavySet W τ, D.δ * (H.card : ℝ))
          = ((Sieve.MTCore.heavySet W τ).card : ℝ) * (D.δ * (H.card : ℝ)) := by
      simp [Finset.sum_const, nsmul_eq_mul, mul_comm, mul_assoc]
    -- From the constant-sum identity and `hsum`, get the canonical product shape:
    have hconst :
      ((Sieve.MTCore.heavySet W τ).card : ℝ) * (D.δ * (H.card : ℝ))
        ≤ ∑ n ∈ Sieve.MTCore.heavySet W τ,
            Sieve.Stage3.windowSum H (Sieve.Stage3.hitIndicator HS) n := by
      simpa [hleft] using hsum
    -- Reorder factors to match `(|heavy|) * c` with `c = δ * |H|`.
    simpa [mul_comm, mul_left_comm, mul_assoc] using hconst
}

/-- Quick smoke: compiles and references. -/
theorem density_to_firstMomentVar_wired (D : WindowDensityLower) : True := by
  let _F : FirstMomentVar := FirstMomentVar_ofDensity D
  exact True.intro

end Analytic
end Sieve
