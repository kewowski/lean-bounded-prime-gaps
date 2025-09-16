import Mathlib
import MaynardTao.SelbergWeights
import MaynardTao.Inequalities

/-!
MaynardTao/SelbergDemo.lean
---------------------------
A tiny, concrete demo of using Selberg-style square weights, showing:
* how to build a simple weight,
* that the global inequality `RCrit` applies to it immediately.
-/

namespace MaynardTao
namespace SelbergDemo

open scoped BigOperators

/-- Example Selberg index set: {1,2,3,4}. -/
def exI : Finset ℕ := (Finset.range 5).filter (fun d => 0 < d)

/-- Example coefficients: weight 1 on d=1, 0 otherwise. -/
def exLam (d : ℕ) : ℚ := if d = 1 then 1 else 0

/-- Example Selberg weight supported on n ≤ N. -/
noncomputable def exW {P : WeightParams} (N : ℕ) : SieveWeight P :=
  SelbergWeights.ofLamOnRange (P := P) exI exLam N

/-- The constructed weight is pointwise nonnegative. -/
lemma exW_nonneg {P : WeightParams} (N n : ℕ) :
    0 ≤ (exW (P := P) N).w n :=
  (exW (P := P) N).nonneg n

/-- The global Maynard–Tao inequality holds for the example weight. -/
lemma exW_RCrit_all {P : WeightParams} (N : ℕ) (H : Finset ℤ) (r : ℕ) :
    Inequalities.RCrit (W := exW (P := P) N) N H r := by
  simpa using Inequalities.RCrit_all (W := exW (P := P) N) N H r

end SelbergDemo
end MaynardTao
