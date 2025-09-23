/-
  Sieve/Analytic/ResidueAI.lean
  UTF-8 (no BOM), ASCII-only.

  Signature-only scaffold:
  Minimal adapter `AI_from_residuePointwise` to keep the residue→density route
  wired without introducing heavy dependencies. No `sorry`, lint-clean.
-/
import Sieve.Analytic.BVMainRealize

namespace Sieve.Analytic

/-- Temporary identity adapter:
    When a per-point residue inequality yields an `AvgWindowHitLB`, pass it here.
    Keeps call-sites stable while residue machinery is completed. -/
@[inline] def AI_from_residuePointwise (AI : AvgWindowHitLB) : AvgWindowHitLB := AI

end Sieve.Analytic
