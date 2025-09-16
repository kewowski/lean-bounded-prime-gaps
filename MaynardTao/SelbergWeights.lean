import Mathlib
import MaynardTao.SquareWeights
import MaynardTao.WeightsAPI

/-!
MaynardTao/SelbergWeights.lean
------------------------------
A minimal Selberg-style square-weight builder specialized from `SquareWeights`:

* Index set `I : Finset ℕ` with coefficients `lam : ℕ → ℚ`.
* Predicates `φ d n := d ∣ n` (divisibility).
* Build a nonnegative weight on `n ≤ N`:
    `W(n) = (∑ d∈I, lam d * 1_{d∣n})^2` for `n ≤ N`, else `0`.
-/

namespace MaynardTao
namespace SelbergWeights

open scoped BigOperators

/-- Divisibility predicate for Selberg-style weights. -/
@[simp] def phiDiv (d n : ℕ) : Prop := d ∣ n

/-- Decidability for `n ↦ d ∣ n`. -/
instance phiDiv_decidable (d : ℕ) : DecidablePred (phiDiv d) := by
  intro n
  change Decidable (d ∣ n)
  infer_instance

/-- Build a Selberg-style square weight on `n ≤ N` using divisibility predicates. -/
noncomputable def ofLamOnRange
    {P : WeightParams} (I : Finset ℕ) (lam : ℕ → ℚ) (N : ℕ) : SieveWeight P :=
  SquareWeights.ofSquareFamilyOnRange
    (P := P) (ι := ℕ) I lam (fun d n => phiDiv d n) N

/-- Unfolding lemma (definitionally the same as the square-family builder). -/
@[simp] lemma ofLamOnRange_def
    {P : WeightParams} (I : Finset ℕ) (lam : ℕ → ℚ) (N : ℕ) :
    ofLamOnRange (P := P) I lam N
      = SquareWeights.ofSquareFamilyOnRange
          (P := P) (ι := ℕ) I lam (fun d n => phiDiv d n) N := rfl

end SelbergWeights
end MaynardTao
