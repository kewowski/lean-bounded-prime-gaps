import Mathlib
import MaynardTao.SelbergWeights
import MaynardTao.Normalize
import MaynardTao.WeightsAPI

/-!
MaynardTao/SelbergNormalized.lean
---------------------------------
Convenience wrapper: build a Selberg weight and normalize it to total mass 1.

Usage:
* Provide an index set `I : Finset ℕ`, coefficients `lam : ℕ → ℚ`, and cutoff `N`.
* Supply a proof that the (unnormalized) total mass is positive.
-/

namespace MaynardTao
namespace SelbergWeights

open SieveWeight

variable {P : WeightParams}

/-- Normalized Selberg-style weight on `n ≤ N`.
Requires a proof `hpos` that the unnormalized total mass is positive. -/
noncomputable def normalized
    (I : Finset ℕ) (lam : ℕ → ℚ) (N : ℕ)
    (hpos : 0 < (ofLamOnRange (P := P) I lam N).total) : SieveWeight P :=
  (ofLamOnRange (P := P) I lam N).normalize hpos

@[simp] lemma total_normalized
    (I : Finset ℕ) (lam : ℕ → ℚ) (N : ℕ)
    (hpos : 0 < (ofLamOnRange (P := P) I lam N).total) :
    (normalized (P := P) I lam N hpos).total = 1 := by
  simpa [normalized] using
    (SieveWeight.total_normalize (W := ofLamOnRange (P := P) I lam N) hpos)

end SelbergWeights
end MaynardTao
