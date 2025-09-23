/-
  Sieve/Analytic/WeightedResidueConst.lean
  Convenience lemmas for constant weights in `residueSumW`.
-/
import Mathlib
import Sieve.Analytic.ResidueSumBasics
import Sieve.Analytic.WeightedResidue

noncomputable section
open Classical BigOperators

namespace Sieve
namespace Analytic

/-- Constant weight convenience: just an alias of `residueSumW_const_weight`. -/
@[simp] lemma residueSumW_const
    (a : ℕ → ℂ) (c : ℝ) (N q : ℕ) (r : ZMod q.succ) :
    residueSumW a (fun _ => c) N q r = (c : ℂ) * residueSum a N q r := by
  simpa using residueSumW_const_weight a c N q r

/-- With constant weight `1`, we recover `residueSum`. -/
@[simp] lemma residueSumW_one
    (a : ℕ → ℂ) (N q : ℕ) (r : ZMod q.succ) :
    residueSumW a (fun _ => (1 : ℝ)) N q r = residueSum a N q r := by
  calc
    residueSumW a (fun _ => (1 : ℝ)) N q r
        = ((1 : ℝ) : ℂ) * residueSum a N q r := residueSumW_const_weight a 1 N q r
    _   = residueSum a N q r := by simp

/-- With constant weight `0`, the weighted residue sum vanishes. -/
@[simp] lemma residueSumW_zero_weight
    (a : ℕ → ℂ) (N q : ℕ) (r : ZMod q.succ) :
    residueSumW a (fun _ => (0 : ℝ)) N q r = 0 := by
  calc
    residueSumW a (fun _ => (0 : ℝ)) N q r
        = ((0 : ℝ) : ℂ) * residueSum a N q r := residueSumW_const_weight a 0 N q r
    _   = 0 := by simp

end Analytic
end Sieve
