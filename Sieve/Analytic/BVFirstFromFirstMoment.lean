/-
  Sieve/Analytic/BVFirstFromFirstMoment.lean

  Bridge pieces from a *first-moment* lower bound:
  If for some constant `c` we have
      (|heavy| : ℝ) * c ≤ ∑_{n∈heavy} windowSum H hitIndicator n
  for every `(W, τ, H, HS)` with heavy nonempty, then `B := c` satisfies
      B ≤ avgOver heavy (windowSum …),
  yielding a realized `AvgWindowHitLB` via the existing skeleton.
-/
import Mathlib
import Sieve.Analytic.BVMainDeriveFromToolbox
import Sieve.Analytic.AvgFromFirstMoment

noncomputable section
open Classical

namespace Sieve
namespace Analytic

/-- Assumption bundle to drive a *first-moment* based bridge. -/
structure FirstMomentPieces (P : BVParams) where
  c : ℝ
  lower_le_c :
    P.lowerFormula ≤ c
  sum_ge :
    ∀ (W : Sieve.MaynardWeights.Weight) (τ : ℝ)
      (H : Finset ℤ) (HS : Sieve.Stage3.HitSystem)
      (_hne : (Sieve.MTCore.heavySet W τ).Nonempty),
      ((Sieve.MTCore.heavySet W τ).card : ℝ) * c
        ≤ ∑ n ∈ Sieve.MTCore.heavySet W τ,
            Sieve.Stage3.windowSum H (Sieve.Stage3.hitIndicator HS) n

/-- Package `FirstMomentPieces` as `BVBridgePieces P`. -/
def BVPieces_fromFirstMoment (P : BVParams) (F : FirstMomentPieces P) :
    BVBridgePieces P where
  B := F.c
  lower_le_B := F.lower_le_c
  B_le_avg := by
    intro W τ H HS hne
    -- Use the heavy-set specialization: sum ≥ |heavy|*c ⇒ average ≥ c
    exact avgOver_heavy_ge_of_sum_ge (W := W) (τ := τ) (H := H) (HS := HS)
      (hne := hne) (c := F.c) (h := F.sum_ge W τ H HS hne)

/-- Build a realized analytic interface from `FirstMomentPieces`. -/
def AI_fromFirstMoment (P : BVParams) (TB : BVToolboxProgressionsSig)
    (F : FirstMomentPieces P) : AvgWindowHitLB :=
  AvgWindowHitLB_fromPieces P TB (BVPieces_fromFirstMoment P F)

/-- Tiny smoke check: the function compiles and wires through. -/
theorem firstMoment_bridge_wired
    (P : BVParams) (TB : BVToolboxProgressionsSig)
    (F : FirstMomentPieces P) : True := by
  let _AI : AvgWindowHitLB := AI_fromFirstMoment P TB F
  exact True.intro

end Analytic
end Sieve
