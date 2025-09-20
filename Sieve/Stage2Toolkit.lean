/-
  Sieve/Stage2Toolkit.lean
  Lightweight re-export hub for Stage 2 lemmas you’ll use downstream.
-/
import Sieve.Stage2Basic
import Sieve.Stage2Average
import Sieve.Stage2Thresholds
import Sieve.Stage2Density
import Sieve.Stage2Pigeonhole
import Sieve.Stage2Max

namespace Sieve.Stage2
/-!  This file intentionally contains no new lemmas:
     it centralizes imports so downstream code can do:
       `import Sieve.Stage2Toolkit`
     and get the whole Stage-2 surface area. -/
end Sieve.Stage2
