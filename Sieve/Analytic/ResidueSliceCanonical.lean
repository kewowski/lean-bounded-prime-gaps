/-
  Sieve/Analytic/ResidueSliceCanonical.lean

  Canonical residue slice:
    contrib(q; H, HS; n, r) = sum over h ∈ H with h mod q = r of the hit indicator at n+h.

  Notes
  -----
  • We *do not* prove the decomposition here; we only define the slice and show nonnegativity.
  • Underscore-prefixed binders silence unused-variable linters while keeping the surface shape.
-/
import Mathlib
import Sieve.Stage3
import Sieve.Stage3Window
import Sieve.Stage3PrimeFacade

noncomputable section
open Classical

namespace Sieve
namespace Analytic

/-- Canonical residue-r contribution at point `n`: sum over `h ∈ H` with `h mod q = r`. -/
def canonicalResidueContrib
    (q : ℕ)
    (_W : Sieve.MaynardWeights.Weight) (_τ : ℝ)
    (H : Finset ℤ) (HS : Sieve.Stage3.HitSystem)
    (n : ℤ) (r : ℕ) : ℝ :=
  ∑ h ∈ H.filter (fun h => (h % (q : ℤ)) = (r : ℤ)),
    Sieve.Stage3.hitIndicator HS (n + h)

/-- Nonnegativity: every canonical residue slice is a sum of 0/1s. -/
lemma canonicalResidueContrib_nonneg
    (q : ℕ)
    (_W : Sieve.MaynardWeights.Weight) (_τ : ℝ)
    (H : Finset ℤ) (HS : Sieve.Stage3.HitSystem)
    (n : ℤ) (r : ℕ) :
    0 ≤ canonicalResidueContrib q _W _τ H HS n r := by
  classical
  unfold canonicalResidueContrib
  refine Finset.sum_nonneg ?hnonneg
  intro h hh
  by_cases hp : HS.isHit (n + h)
  · simp [Sieve.Stage3.hitIndicator, hp]
  · simp [Sieve.Stage3.hitIndicator, hp]

/-- Smoke: keep the surface watched. -/
theorem canonicalResidueContrib_wired : True := by
  let _ := @canonicalResidueContrib
  let _ := @canonicalResidueContrib_nonneg
  exact True.intro

end Analytic
end Sieve
