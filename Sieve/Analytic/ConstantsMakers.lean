/-
  Sieve/Analytic/ConstantsMakers.lean
  UTF-8 (no BOM), ASCII-only.

  Purpose
  -------
  Tiny BV parameter constructors and algebraic convenience lemmas that are
  *trivially* provable. Kept lightweight to stay green.

  House rules:
  • Leaf module (imports only small analytic leaves).
  • Proofs are tiny (`simp`/`rw`), no heavy tactics.
-/
import Mathlib
import Sieve.Analytic.Constants
import Sieve.Analytic.BVMainAssumptions

noncomputable section

namespace Sieve
namespace Analytic

/-- Factory: build `BVParams` with zero error constants. -/
def BVParams.mkZeroErrors
    (N : ℕ) (hN2 : 2 ≤ N)
    (Cmain threshold : ℝ)
    (logN_pos : 0 < Real.log (N : ℝ)) : BVParams :=
{ N := N
, hN2 := hN2
, Cmain := Cmain
, Cerr1 := 0
, Cerr2 := 0
, threshold := threshold
, logN_pos := logN_pos }

/-- With zero error constants, `lowerFormula = Cmain`. -/
lemma BVParams.lowerFormula_mkZeroErrors
    (N : ℕ) (hN2 : 2 ≤ N) (Cmain threshold : ℝ)
    (logN_pos : 0 < Real.log (N : ℝ)) :
    (BVParams.mkZeroErrors N hN2 Cmain threshold logN_pos).lowerFormula = Cmain := by
  simp [BVParams.mkZeroErrors, BVParams.lowerFormula]

/--
Trivial assumption bundle when both error constants and the threshold are zero,
provided `Cmain` is nonnegative. This keeps later demos simple and fast.
-/
def BVMainAssumptions.mkZero
    (P : BVParams) (hC1 : P.Cerr1 = 0) (hC2 : P.Cerr2 = 0)
    (hT : P.threshold = 0) (hCmain_nonneg : 0 ≤ P.Cmain) : BVMainAssumptions P :=
{ Cerr1_nonneg := by simp [hC1]
, Cerr2_nonneg := by simp [hC2]
, lb_ready := by
    have hlf : P.lowerFormula = P.Cmain := by
      simp [BVParams.lowerFormula, BVParams.logN, hC1, hC2]
    -- Goal: `P.lowerFormula ≥ P.threshold`; rewrite both sides.
    -- becomes `P.Cmain ≥ 0`, which is `hCmain_nonneg`.
    simpa [hlf, hT, ge_iff_le] using hCmain_nonneg }

/--
If `Cerr1 = Cerr2 = 0`, then `threshold ≤ Cmain` implies
`threshold ≤ lowerFormula` (since `lowerFormula = Cmain`).
-/
lemma threshold_le_lower_of_zeroErrors
    (P : BVParams) (hC1 : P.Cerr1 = 0) (hC2 : P.Cerr2 = 0)
    (hTle : P.threshold ≤ P.Cmain) :
    P.threshold ≤ P.lowerFormula := by
  have hlf : P.lowerFormula = P.Cmain := by
    simp [BVParams.lowerFormula, BVParams.logN, hC1, hC2]
  simpa [hlf] using hTle

end Analytic
end Sieve
