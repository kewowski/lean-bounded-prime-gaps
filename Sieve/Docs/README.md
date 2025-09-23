# Bridge Hub Quickstart

Import this hub wherever you are writing demos or top-level apps:

    import Sieve.Analytic.BridgeHub

You get:

- `ToolboxSig` (`BVToolboxProgressionsSig`) — signatures-only large-sieve / orthogonality / partial-summation shapes.
- `ToolboxAPI P` (`BVToolboxAPI P`) — bundle with `derive : BVMainIneq P`.
- `BridgePieces P` — constant `B` with `lower ≤ B` and `B ≤ average …` to compose into the gateway.
- `DeriveFromToolbox P TB bp : BVMainIneq P` — compose pieces (algebra-only).
- `AvgWindowHitLBOf P api : AvgWindowHitLB` — package API into Stage-3 interface.
- `AvgWindowHitLBFromPieces P TB bp : AvgWindowHitLB` — package pieces directly.

House Rules:
- Do **not** import this hub from analytic leaf modules. Demos may import hubs.
- Keep proofs tiny; fix linters immediately.
