/-
  Sieve/Analytic/BridgeHub.lean
  UTF-8 (no BOM), ASCII-only.

  Purpose
  -------
  Convenience **hub** for demos and downstream ergonomics.
  Import the typed analytic-bridge pieces so callers can
  `import Sieve.Analytic.BridgeHub` and get everything they need
  without touching leaf modules.

  House rule reminder:
  • **Do not import this hub from analytic leaf modules.**
    Demos and top-level apps may import hubs; core analytic leaves must remain light.
-/
import Mathlib
-- Leafy analytic pieces (safe to re-export via hub):
import Sieve.Analytic.Constants
import Sieve.Analytic.BVMainAssumptions
import Sieve.Analytic.AIConstructors
import Sieve.Analytic.BVMainRealize
import Sieve.Analytic.BVMainIneq
import Sieve.Analytic.BVToolboxProgressionsSig
import Sieve.Analytic.BVToolboxAPI
import Sieve.Analytic.BVMainDeriveFromToolbox
import Sieve.Analytic.ProgressionsCorollaries

-- Stage-3 bridge (consumed by demos/apps; not by analytic leaves)
import Sieve.AnalyticBridge

noncomputable section

namespace Sieve
namespace Analytic

/-- Hub compiles sanity. Keep this trivial to avoid any dependencies. -/
theorem bridge_hub_compiles : True := True.intro

/-!
  Lightweight **abbrev re-exports** for downstream ergonomics.
  These are aliases only; they do not add dependencies beyond what is already imported above.
-/

/-- Alias for the per-parameter bridge payload used to derive the gateway inequality. -/
abbrev BridgePieces (P : BVParams) := BVBridgePieces P

/-- Alias names for toolbox signatures and API. -/
abbrev ToolboxSig := BVToolboxProgressionsSig
abbrev ToolboxAPI (P : BVParams) := BVToolboxAPI P

/-- Alias for composing toolbox + pieces into the single gateway inequality. -/
abbrev DeriveFromToolbox (P : BVParams) (TB : ToolboxSig) (bp : BridgePieces P) :
    BVMainIneq P :=
  deriveFromToolbox P TB bp

/-- Alias for packaging an API into the Stage-3 analytic interface. -/
abbrev AvgWindowHitLBOf (P : BVParams) (api : ToolboxAPI P) : AvgWindowHitLB :=
  AvgWindowHitLB_of P api

/-- Alias for packaging bridge pieces (constant lower + bound-to-avg) into the interface. -/
abbrev AvgWindowHitLBFromPieces (P : BVParams) (TB : ToolboxSig) (bp : BridgePieces P) :
    AvgWindowHitLB :=
  AvgWindowHitLB_fromPieces P TB bp

end Analytic
end Sieve
