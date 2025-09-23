/-
  Sieve/Analytic/BVMainRealize.lean
  UTF-8 (no BOM), ASCII-only.

  Purpose
  -------
  A tiny, *real* constructor that turns a BV lower bound (`P.lowerFormula`)
  into the Stage-3 analytic interface `AvgWindowHitLB` **once you provide**
  the analytic inequality showing this lower bound is ≤ the Stage-3 average.

  This keeps Stage-2/3 code unchanged: callers supply the inequality,
  and we package it with the constant-in-(W,τ,H,HS) lower function.

  No heavy analysis here—just typed plumbing.
-/
import Mathlib
import Sieve.Analytic.Constants
import Sieve.AnalyticInputs
import Sieve.Analytic.AIConstructors
import Sieve.Analytic.BVMainAssumptions

noncomputable section

namespace Sieve
namespace Analytic

open AnalyticInputs

/--
Build an `AvgWindowHitLB` using the *BV lower formula* as a constant lower bound,
provided a proof that this lower bound is ≤ the Stage-3 average for every
`(W, τ, H, HS)` and nonempty heavy set.

This is the point where BV/EH (or any analytic input) plugs in a single inequality.
-/
def AI_of_BV_fromLowerBound (P : BVParams)
  (h :
    ∀ (W : Sieve.MaynardWeights.Weight) (τ : ℝ)
      (H : Finset ℤ) (HS : Sieve.Stage3.HitSystem)
      (_hne : (Sieve.MTCore.heavySet W τ).Nonempty),
      P.lowerFormula
        ≤ Sieve.Stage3.avgOver (Sieve.MTCore.heavySet W τ)
            (Sieve.Stage3.windowSum H (Sieve.Stage3.hitIndicator HS)))
  : AvgWindowHitLB :=
  AnalyticInputs.ofLower
    (fun _W _τ _H _HS _hne => P.lowerFormula)
    (fun W τ H HS hne => h W τ H HS hne)

/-- A convenience wrapper that also carries a `BVMainAssumptions P` (currently unused here). -/
def AI_of_BV_fromLowerBound' (P : BVParams) (_A : BVMainAssumptions P)
  (h :
    ∀ (W : Sieve.MaynardWeights.Weight) (τ : ℝ)
      (H : Finset ℤ) (HS : Sieve.Stage3.HitSystem)
      (_hne : (Sieve.MTCore.heavySet W τ).Nonempty),
      P.lowerFormula
        ≤ Sieve.Stage3.avgOver (Sieve.MTCore.heavySet W τ)
            (Sieve.Stage3.windowSum H (Sieve.Stage3.hitIndicator HS)))
  : AvgWindowHitLB :=
  AI_of_BV_fromLowerBound P h

end Analytic
end Sieve
