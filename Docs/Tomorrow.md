# Tomorrow — checklist & plan

## Quick checks (keep green)
- `lake build` once at the start to warm cache.
- No `sorry`, no new `axiom` declarations, no hub imports in analytic leaves.
- If a smoke just “touches” a theorem, use `let _ := @theorem_name` (no dummy instances).

## Target 1 — Residue → Density (pointwise)
- Add `ResidueToDensity.lean`: use `ResiduePartition`, `ResiduePointwise`, `ResiduePigeonhole` to get  
  `windowSum H (hitIndicator HS) n ≥ δ · |H|` for each heavy `n` in canonical `Finset.range`/`filter` shape.
- Provide `WindowDensityLower_ofResidues … : WindowDensityLower`.

## Target 2 — First moment (realized)
- `FirstMomentVar_fromResidues.lean` that builds `FirstMomentVar` from the density constructor.
- Demo: show `δ · |H| ≥ 1 ⇒` heavy hit via `exists_heavy_hit_from_density`.

## Target 3 — Second moment scaffolding
- `PaleyZygmundTemplate.lean` (typed, leaf-only): from `E[X]` and `E[X^2]`, get many heavy points with large windows.
- `SecondMomentAliases.lean`: tiny CS/Chebyshev rewrites.

## Target 4 — LS aliases
- Strengthen `LargeSieveResidueSquares.lean` with the exact squared-residue form Paley–Zygmund will consume.

## Perf & lint hygiene
- Add a single `let _ := @exists_heavy_hit_from_density` touch in `PerfHarness`.
- Prefer `simp` when the goal matches; prune unused simp args; underscore unused binders *in types*.
