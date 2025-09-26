import Mathlib
import Sieve.Stage3Window
import Sieve.Stage3PrimeFacade
import Sieve.Stage3PrimesEndToEnd
import Sieve.Stage3DensityZero
import Sieve.Stage3Monotone
import Sieve.Stage3SecondMomentEmptiness
import Sieve.Stage3AvgConst
import Sieve.Stage3TwinGap
import Sieve.Analytic.BVMainStatement
import Sieve.Analytic.BVMainStatementWrapper
import Sieve.Analytic.BVMainStatementWire
import Sieve.Stage3HeavySetMonotone



/-!
  Sieve/Stage3Exports.lean
  UTF-8 (no BOM), ASCII-only.

  Canonical export hub for Stage-3 modules.
  NOTE: We import `Sieve.Stage3Monotone` (canonical) instead of the deprecated
  `Sieve.Stage3DensityMonotone` to avoid duplicate lemma names such as
  `Sieve.Stage3.heavyDensity_antitone_in_tau`.
-/
