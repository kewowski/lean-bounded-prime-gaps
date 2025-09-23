/-
  Sieve/Analytic/BVMainDeriveFromToolbox.lean
  UTF-8 (no BOM), ASCII-only.

  Purpose
  -------
  Typed, risk-free *skeleton* for deriving the single gateway inequality
  `BVMainIneq P` from a BV/EH-style toolbox. This file does **not** do heavy
  analysis; it just provides the minimal algebraic wiring you will later fill.

  Key idea
  --------
  We separate the derivation into two parts:

  1) A *bridge payload* that picks a constant `B : ℝ` and supplies:
       • `lower_le_B  : P.lowerFormula ≤ B`
       • `B_le_avg    : ∀ (W τ H HS hne), B ≤ avgOver …`
     This is where the analytic work (partial summation → large sieve →
     orthogonality) will live.  In this stage, it’s a parameter.

  2) A tiny wrapper `deriveFromPieces` that composes the two inequalities to
     produce `BVMainIneq P`. This is pure algebra (`le_trans`) and very fast.

  We also provide trivial wrappers that *touch* each field of
  `BVToolboxProgressionsSig` so signature drift will be caught by the compiler.
-/
import Mathlib
import Sieve.Analytic.BVToolboxProgressionsSig
import Sieve.Analytic.BVMainIneq
import Sieve.Analytic.BVMainRealize

noncomputable section
open scoped BigOperators

namespace Sieve
namespace Analytic

/-- Bridge payload: a constant `B` bounding the Stage-3 average from below. -/
structure BVBridgePieces (P : BVParams) where
  B          : ℝ
  lower_le_B :
    P.lowerFormula ≤ B
  B_le_avg   :
    ∀ (W : Sieve.MaynardWeights.Weight) (τ : ℝ)
      (H : Finset ℤ) (HS : Sieve.Stage3.HitSystem)
      (_hne : (Sieve.MTCore.heavySet W τ).Nonempty),
      B ≤ Sieve.Stage3.avgOver (Sieve.MTCore.heavySet W τ)
            (Sieve.Stage3.windowSum H (Sieve.Stage3.hitIndicator HS))

/-- Compose the payload to obtain the single gateway inequality. -/
@[inline] def deriveFromPieces (P : BVParams) (bp : BVBridgePieces P) : BVMainIneq P :=
  by
    intro W τ H HS hne
    exact le_trans bp.lower_le_B (bp.B_le_avg W τ H HS hne)

/-- Same as `deriveFromPieces`, but threaded through the toolbox `TB`.
    (For now `TB` is unused here; future versions may build `bp.B_le_avg` from it.) -/
@[inline] def deriveFromToolbox (P : BVParams)
    (_TB : BVToolboxProgressionsSig) (bp : BVBridgePieces P) : BVMainIneq P :=
  deriveFromPieces P bp

/-- Package the derived inequality into the Stage-3 analytic interface. -/
@[inline] def AvgWindowHitLB_fromPieces (P : BVParams)
    (TB : BVToolboxProgressionsSig) (bp : BVBridgePieces P) : AvgWindowHitLB :=
  AI_of_BV_ofIneq P (deriveFromToolbox P TB bp)

/-!
  Tiny wrappers that *touch* each field of the toolbox signatures.
  These keep the compiler watching the exact shapes, but do no work yet.
-/

/-- Touch large-sieve field (shape only). -/
@[inline] def use_large_sieve_progressions
    (TB : BVToolboxProgressionsSig)
    (q N : ℕ) (a : ℕ → ℝ) :
    (∑ r ∈ Finset.range q,
        (∑ n ∈ (Finset.range (N + 1)).filter (fun n => n % q = r), a n) ^ 2)
      ≤ TB.C_LS * (∑ n ∈ Finset.range (N + 1), (a n) ^ 2) :=
  TB.large_sieve_progressions q N a

/-- Touch orthogonality field (shape only). -/
@[inline] def use_orthogonality_indicator
    (TB : BVToolboxProgressionsSig) (q r : ℕ) :
    (∑ n ∈ Finset.range q, (if n % q = r then (1 : ℝ) else 0))
      = (if r ∈ Finset.range q then (1 : ℝ) else 0) :=
  TB.orthogonality_indicator q r

/-- Touch discrete partial summation field (shape only). -/
@[inline] def use_discrete_partial_summation
    (TB : BVToolboxProgressionsSig) (N : ℕ) (a A : ℕ → ℝ) :
    (∑ n ∈ Finset.range (N + 1), a n)
      = A N - A 0 + (∑ n ∈ Finset.range N, (A n - A (n + 1))) :=
  TB.discrete_partial_summation N a A

/-- Availability sanity: touch `TB` and `bp` so linters stay happy. -/
theorem derive_from_toolbox_wired
    (P : BVParams) (TB : BVToolboxProgressionsSig) (bp : BVBridgePieces P) : True := by
  classical
  -- Touch toolbox pieces
  let _ := TB.C_LS
  have _ := use_orthogonality_indicator TB 1 0
  have _ := use_discrete_partial_summation TB 0 (fun _ => (0 : ℝ)) (fun _ => (0 : ℝ))
  -- Touch bridge pieces and the composed inequality
  let _ : ℝ := bp.B
  have _ := bp.lower_le_B
  have _ := deriveFromToolbox P TB bp
  exact True.intro

end Analytic
end Sieve
