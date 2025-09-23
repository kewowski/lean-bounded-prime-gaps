import Mathlib
import Sieve.Stage3Exports
import Sieve.Stage3Ergonomics
import Sieve.AnalyticBVTemplate
import Sieve.Analytic.BVSketch
import Sieve.Analytic.BVSketchParams

/-!
  Sieve/Stage3ExportsAll.lean
  UTF-8 (no BOM), ASCII-only.

  Convenience hub:
  - Re-exports all Stage-3 machinery via `Sieve.Stage3Exports`.
  - Adds Stage-3 ergonomics helpers (`Sieve.Stage3Ergonomics`).
  - Brings in analytic providers:
      * `Sieve.AnalyticBVTemplate` (mock/template),
      * `Sieve.Analytic.BVSketch` (generic P : ℝ),
      * `Sieve.Analytic.BVSketchParams` (uses `BVParams`).

  Downstream users can `import Sieve.Stage3ExportsAll`
  to get the Stage-3 API + helpers + analytic providers in one line.
-/
