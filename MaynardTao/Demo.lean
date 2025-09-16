import Mathlib
import MaynardTao.AdmissibleTuples
import MaynardTao.WeightsAPI
import MaynardTao.WeightOps
import MaynardTao.Sums
import MaynardTao.WeightBuilders
import MaynardTao.Params

/-!
MaynardTao/Demo.lean
--------------------
Tiny demo wiring together the lightweight APIs:

* `P0`      : trivial admissible params (empty tuple).
* `Wconst`  : constant-1 weight on `range (N+1)`.
* `S0demo`  : baseline sum `S0` for that weight, up to `N`.
-/

namespace MaynardTao
namespace Demo

def P0 : WeightParams := trivialParams

def Wconst (N : ℕ) : SieveWeight P0 :=
  SieveWeight.ofSupport (P := P0) (Finset.range (N + 1)) (1 : ℚ)
    (by exact zero_le_one)
    (by exact one_ne_zero)

def S0demo (N : ℕ) : ℚ :=
  Sums.S0 (W := Wconst N) N

end Demo
end MaynardTao
