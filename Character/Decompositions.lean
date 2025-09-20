/-
  Character/Decompositions.lean
  UTF-8 (no BOM), ASCII-only.
-/
import Mathlib

namespace Character

/-- Marker that the Character API shim is present. -/
def apiReady : Prop := True
@[simp] theorem apiReady_true : apiReady := trivial

/-- Minimal abstract character handle. -/
structure Char (α : Type u) where
  toFun  : Int → α
  isMul  : Prop := True
  period : Nat := 1

/-- Explicit evaluation (we avoid function coercions to keep the API robust). -/
@[inline] def eval {α} (χ : Char α) (n : Int) : α := χ.toFun n

/-- Minimal L²-type summary placeholder. -/
structure L2Summary where
  l2Mass : ℝ

/-- Placeholder Prop stating some decomposition is available. -/
def DecompositionAvailable : Prop := True

@[simp] theorem decomp_available : DecompositionAvailable := trivial

end Character
