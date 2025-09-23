/-
  Sieve/RunAllSmoke.lean
  Aggregates all Stage-3 demo files so they’re exercised together in CI/builds.
-/
import Mathlib
import Sieve.RunStage3TwinGapDemo
import Sieve.RunStage3TwinGapTwinPrimesDemo
import Sieve.RunAnalyticBVTemplateDemo
import Sieve.RunBVSketchTwinDemo
import Sieve.RunBVSketchParamsTwinDemo
import Sieve.RunBVMainStatementDemo

noncomputable section
open Classical

-- Trivial token so the file isn’t empty.
def Sieve.runAllSmoke_ok : True := True.intro
