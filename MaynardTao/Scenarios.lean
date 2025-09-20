import Mathlib
import MaynardTao.BoundedGaps
import MaynardTao.WeightBuilders

/-!
MaynardTao/Scenarios.lean
-------------------------
Tiny helpers to instantiate `BoundedGaps.Spec` for quick experiments.

* `trivialSpec N c hc` : uses the empty admissible tuple and a constant weight `c > 0`
  supported on `range (N+1)`. The target `lambda` is set to `0` by default.
-/

namespace MaynardTao
namespace Scenarios

/-- Build a simple `Spec`:
  * `P`: empty admissible tuple (coherent but with `k = 0`)
  * `W`: constant weight `c > 0` on `range (N+1)`
  * `N`: cutoff
  * `lambda`: default `0` (can be adjusted later if needed)
-/
def trivialSpec (N : ℕ) (c : ℚ) (hc : 0 < c) : BoundedGaps.Spec :=
{ P := trivialParams
, W := SieveWeight.ofSupport (P := trivialParams)
        (Finset.range (N + 1)) c
        (le_of_lt hc) (ne_of_gt hc)
, N := N
, lambda := 0 }

end Scenarios
end MaynardTao
