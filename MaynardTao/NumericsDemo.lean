import Mathlib
import MaynardTao.NumericsAPI
import MaynardTao.Sandwich  -- optional: handy upper bound in comments

/-!
MaynardTao/NumericsDemo.lean
----------------------------
A tiny demo of using `NumericsAPI`:

* Build a `Params` record.
* Assume positivity of the unnormalized Selberg total.
* Assume the numerical inequality `S_{≥ r} ≥ θ · S₀`.
* Conclude `S' ≥ (r : ℚ) · θ · S₀` via `NumericsAPI.criterion`.
-/

namespace MaynardTao
namespace NumericsDemo

open NumericsAPI

/-- Example coefficients: δ_{d=1}. -/
def oneAt1 (d : ℕ) : ℚ := if d = 1 then 1 else 0

/-- Example parameter pack; feel free to customize for experiments. -/
def exParams : Params where
  N   := 1000
  r   := 2
  θ   := (1 : ℚ) / 10
  I   := (Finset.range 5).filter (fun d => 0 < d)
  lam := oneAt1
  H   := ({0, 2, 6} : Finset ℤ)

/-- If the unnormalized Selberg total is positive and the numerical assumption holds,
    then the desired inequality follows. -/
theorem runCriterion
    {P : WeightParams}
    (hpos :
      0 < (SelbergWeights.ofLamOnRange (P := P) exParams.I exParams.lam exParams.N).total)
    (hθ   : Assumption (P := P) exParams hpos) :
    Conclusion (P := P) exParams hpos :=
  NumericsAPI.criterion (P := P) exParams hpos hθ

/-
Notes:
* To *use* this, provide a proof of `hpos` (positivity of the raw Selberg total)
  and the numeric inequality `hθ`. Then `runCriterion` gives the global bound.
* You can also combine with `Sandwich.right` to get an a priori upper bound:
  S' ≤ |H| · S₀, useful to sanity-check θ ranges.
-/

end NumericsDemo
end MaynardTao
