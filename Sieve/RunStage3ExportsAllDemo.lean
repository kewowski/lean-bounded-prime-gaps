/-
  Sieve/RunStage3ExportsAllDemo.lean
  Smoke test: one-line import ensures Stage-3 API + analytic template visible.
-/
import Mathlib
import Sieve.Stage3ExportsAll

noncomputable section
open Classical

-- Trivial token so the file isn’t empty.
def Sieve.stage3ExportsAll_demo_ok : True := True.intro
