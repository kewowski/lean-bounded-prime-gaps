## Stage-3 Twin Gap & Analytic Template (new)

- Sieve/Stage3TwinGap.lean
  - 	winOffsets := {0,2} with basic facts.
  - xists_twin_window_with_two_primes_of_AI_ge_two_from_avg — k=2 specialization (average ≥ 2 ⇒ at least two primes in twin window).
  - 	win_window_card_ge_two_imp_twin_primes — local extraction (no analytics): if the filtered {0,2} window has card ≥ 2, then 
 and 
+2 are both prime.
  - xists_twin_primes_of_AI_ge_two_from_avg — main wrapper (prime façade): with heavy-set derived from τ ≤ average and analytic lower bound ≥ 2, produce a twin prime pair.

- Demos:
  - Sieve/RunStage3TwinGapTwinPrimesDemo.lean — mock AI (avgAsLower) ⇒ twin primes from ≥ 2.
  - Sieve/RunAnalyticBVTemplateDemo.lean — shows how a BV/EH-style AI (template) plugs into Stage-3 wrappers.

- Analytic template:
  - Sieve/AnalyticBVTemplate.lean — alias to vgAsLower; replace with real BV/EH bound by filling .lower and .le_avg.

## Convenience Hub

- Sieve/Stage3ExportsAll.lean
  - Re-exports all Stage-3 modules via Sieve.Stage3Exports.
  - Also imports the BV/EH analytic template (Sieve.AnalyticBVTemplate).
  - **Use:** import Sieve.Stage3ExportsAll to get the Stage-3 API + analytic template in one line.
## Analytic Layer (BV/EH Sketch) — new

- Sieve/Analytic/Constants.lean — BVParams (θ, k, Cmain, Cerr, x0).
- Sieve/Analytic/LargeSieveCore.lean — BVToolbox placeholders (large sieve, orthogonality, partial summation).
- Sieve/Analytic/BVSketch.lean — generic sketch provider:
  - lowerFormula (P : Type) … := 0 (placeholder),
  - vSketch P TB proof : AvgWindowHitLB (hard analysis passed as proof argument).
- Sieve/Analytic/BVSketchParams.lean — BVParams-specialized provider:
  - lowerFormulaParams P … := P.Cmain - P.Cerr,
  - vSketchParams P TB proof : AvgWindowHitLB.

### Demos

- Sieve/RunBVSketchTwinDemo.lean — uses vSketch (generic P : Type) to show ≥1 / ≥2 ⇒ primes/twins.
- Sieve/RunBVSketchParamsTwinDemo.lean — same with BVParams.
- Sieve/RunAllSmoke.lean — aggregates all demos (twin + BV templates/sketches).

### Notes

- Analytic modules are leaf-like; avoid importing big Stage-3 hubs inside them to prevent cycles.
- Stage-3 wrappers consume any AvgWindowHitLB (e.g. from vSketch/vSketchParams).
## BV/EH Main Statement (new)

- Sieve/Analytic/BVMainStatement.lean
  - BVMainStatement P TB : Prop — single inequality target that feeds Stage-3.
  - AI_of_BV P TB h : AvgWindowHitLB — turns any proof h into a provider.

### Demo
- Sieve/RunBVMainStatementDemo.lean — shows how AI_of_BV yields ≥1 / ≥2 conclusions.

