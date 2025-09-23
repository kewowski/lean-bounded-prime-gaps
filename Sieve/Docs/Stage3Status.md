# Stage-3 Status & Next Steps

**Status:** ✅ *Typed bridge complete and green.*

We now have a stable, leaf-friendly analytic bridge from BV/EH inputs to Stage-3:
- Single gateway: `BVMainIneq P`
- Realizers: `AI_of_BV_ofIneq`, `AI_of_BV_fromLowerBound`, `AvgWindowHitLB_fromPieces`
- Signatures toolbox: `BVToolboxProgressionsSig`, `BVToolboxAPI`
- Derivation skeleton: `BVBridgePieces`, `deriveFromPieces`, `deriveFromToolbox`
- Corollaries (leaf, algebraic): `ProgressionsCorollaries`
- Hubs/Smoke/Perf: `BridgeHub`, `RunBVToolboxAPISmoke`, `RunBVPiecesBridgeSmoke`, `PerfHarness`

Everything compiles quickly; demos and perf harness catch signature drift.

---

## What remains (to *finish* the BV/EH analytic route)

These steps are outside the Stage-3 *typed bridge* and are the start of the heavy analysis, but we’ll keep them incremental and leaf-only.

### 1) Build the actual lower bound `B ≤ average …`
Prove a concrete `B_le_avg` for a chosen `P : BVParams`:

1. **Discrete partial summation** (shape ready: `dps_rearranged`).
2. **Orthogonality** for residue indicators/characters (we have an impl; use it to linearize).
3. **Large sieve over progressions** (use `large_sieve_total_bound`) to control the L² term.
4. **Assemble constants** using `ConstantsMakers` / `BVAlgebraLemmas` (already minimal and fast).

This yields `BVBridgePieces P` with your chosen `B`, then
`AvgWindowHitLB_fromPieces P TB bp : AvgWindowHitLB`.

### 2) Instantiate a first concrete parameter pack
Pick a very gentle `P` (e.g., `lowerFormula = 0` or a tiny positive constant from trivial bounds) and show the inequality holds — this gives a **working** realized AI:
- File: `Sieve/Analytic/BVFirstRealization.lean` (leaf)
- Output: `def AI_first : AvgWindowHitLB := AvgWindowHitLB_fromPieces P TB bp`

### 3) Demo: primes/twins via realized AI
Add a thin demo that imports `BridgeHub` and applies Stage-3 extraction with the realized AI:
- `RunBVFirstRealizationDemo.lean`: “if lower ≥ 1 ⇒ hit/prime in window”.

### 4) Perf guard bump (optional)
Add one line in `PerfHarness.lean` referencing `AI_first` so regressions are caught.

---

## Files to touch next (proposed)
- `Sieve/Analytic/BVFirstRealization.lean` — prove a toy `B_le_avg` (via DPS + orthogonality + LS) and package `AI_first`.
- `Sieve/Analytic/RunBVFirstRealizationDemo.lean` — small demo using `AI_first`.

> We will keep each step tiny (algebraic rewrites, no heavy tactics), leaf-imports only, and run a per-file build after each edit.

