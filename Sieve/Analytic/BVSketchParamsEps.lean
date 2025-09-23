/-
  Sieve/Analytic/BVSketchParamsEps.lean
  Extended BV sketch parameters with an explicit epsilon-loss,
  and a clean lower-formula that subtracts both error and epsilon.

  Purpose:
    Keep Stage-2/3 stable while allowing analytic providers to carry a
    small loss term `ε` in addition to the main-minus-error split.

  Contents:
    • `BVParamsEps`                       : carries `Cmain`, `Cerr`, `eps`.
    • `lowerFormulaParamsEps P = Cmain - Cerr - eps`.
    • Algebraic rewrites and a nonnegativity lemma under a simple bound.
-/
import Mathlib

noncomputable section
open Classical

namespace Sieve
namespace Analytic

/-- Parameters for a BV-style lower bound with an explicit epsilon-loss. -/
structure BVParamsEps where
  Cmain : ℝ
  Cerr  : ℝ
  eps   : ℝ
deriving Repr, Inhabited

/-- Convenience constructor (spells out field names to keep call sites clear). -/
@[simp] def mkBVParamsEps (Cmain Cerr eps : ℝ) : BVParamsEps :=
  { Cmain := Cmain, Cerr := Cerr, eps := eps }

/-- The lower bound formula carried by the params: `main - error - eps`. -/
def lowerFormulaParamsEps (P : BVParamsEps) : ℝ := P.Cmain - P.Cerr - P.eps

@[simp] lemma lowerFormulaParamsEps_def (P : BVParamsEps) :
    lowerFormulaParamsEps P = P.Cmain - P.Cerr - P.eps := rfl

/-- A handy rewrite: `main - error - eps = main - (error + eps)`. -/
lemma lowerFormulaParamsEps_eq_main_sub_sum (P : BVParamsEps) :
    lowerFormulaParamsEps P = P.Cmain - (P.Cerr + P.eps) := by
  -- `a - (b + c) = a - b - c`, so we flip that identity.
  simpa [lowerFormulaParamsEps] using (sub_add (P.Cmain) (P.Cerr) (P.eps)).symm

/--
If `Cerr + eps ≤ Cmain`, then the lower formula is nonnegative.

Typical use: `Cerr ≤ α / log N` and `eps ≤ β / log N` with `(α + β) ≤ Cmain`.
-/
lemma lowerFormulaParamsEps_nonneg_of_sum_le (P : BVParamsEps)
    (h : P.Cerr + P.eps ≤ P.Cmain) :
    0 ≤ lowerFormulaParamsEps P := by
  -- Rewrite as a single subtraction and apply `sub_nonneg`.
  have := sub_nonneg.mpr h
  simpa [lowerFormulaParamsEps_eq_main_sub_sum] using this

/--
Monotonicity in `Cmain`: increasing `Cmain` increases the lower formula,
holding `Cerr, eps` fixed.
-/
lemma lowerFormulaParamsEps_mono_in_Cmain
    {P P' : BVParamsEps} (hC : P.Cmain ≤ P'.Cmain)
    (hE : P.Cerr = P'.Cerr) (hε : P.eps = P'.eps) :
    lowerFormulaParamsEps P ≤ lowerFormulaParamsEps P' := by
  have : P.Cmain - (P.Cerr + P.eps) ≤ P'.Cmain - (P'.Cerr + P'.eps) := by
    simpa [hE, hε] using sub_le_sub_right hC _
  simpa [lowerFormulaParamsEps_eq_main_sub_sum, hE, hε] using this

/--
Antitonicity in the loss: increasing the combined loss `Cerr + eps`
decreases the lower formula (with `Cmain` fixed). This version is stated
as separate monotonicity in `Cerr`; an identical lemma holds for `eps`.
-/
lemma lowerFormulaParamsEps_antitone_in_Cerr
    {P P' : BVParamsEps} (hC : P.Cmain = P'.Cmain)
    (hε : P.eps = P'.eps) (hE : P.Cerr ≤ P'.Cerr) :
    lowerFormulaParamsEps P ≥ lowerFormulaParamsEps P' := by
  have : P.Cmain - (P.Cerr + P.eps) ≥ P'.Cmain - (P'.Cerr + P'.eps) := by
    -- `a - x` is antitone in `x`.
    have hx : (P'.Cerr + P'.eps) ≤ (P.Cerr + P.eps) := by
      -- from `P.Cerr ≤ P'.Cerr` we get `P'.Cerr + eps ≤ P.Cerr + eps`
      -- then flip sides for antitone; easier to rewrite targets first:
      -- We'll prove `(P.Cerr + P.eps) ≥ (P'.Cerr + P'.eps)`.
      simpa [hε] using add_le_add_right hE _
    -- Now `a - (b') ≤ a - (b)` implies `a - b ≥ a - b'`.
    have := sub_le_sub_left hx P.Cmain
    -- Flip inequality direction and rewrite targets to match.
    simpa using this
  simpa [lowerFormulaParamsEps_eq_main_sub_sum, hC, hε] using this

end Analytic
end Sieve
