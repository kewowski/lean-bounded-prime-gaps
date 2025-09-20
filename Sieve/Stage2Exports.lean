/-
  Sieve/Stage2Exports.lean
  One-stop hub for Stage 2. Imports Stage-2 modules and (where needed)
  re-exports symbols from non-`Sieve.Stage2` namespaces into `Sieve.Stage2`.
-/
import Sieve.Stage2
import Sieve.Stage2Average
import Sieve.Stage2AvgNonneg
import Sieve.Stage2Basic
import Sieve.Stage2Density
import Sieve.Stage2DensitySecond
import Sieve.Stage2Glue
import Sieve.Stage2Max
import Sieve.Stage2Monotone
import Sieve.Stage2MonotoneThresholds
import Sieve.Stage2Pigeonhole
import Sieve.Stage2Report
import Sieve.Stage2Squared
import Sieve.Stage2Summary
import Sieve.Stage2Thresholds
import Sieve.Stage2Toolkit
import Sieve.Stage2SecondMoment
import Sieve.Stage2SecondMomentExtras
import Sieve.Stage2BoundsFromEq
import Sieve.Stage2Weight
import Sieve.Stage2MinBounds
import Sieve.Stage2FirstMomentExtras

namespace Sieve.Stage2
  -- Re-export only from foreign namespaces (OK).
  export Sieve.Stage2SecondMoment
    ( heavy_count_le_of_secondMoment
      heavy_count_strict_le_of_secondMoment
      heavy_strict_empty_of_secondMoment_lt
      heavy_nonstrict_empty_of_secondMoment_lt )
end Sieve.Stage2
