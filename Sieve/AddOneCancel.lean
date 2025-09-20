/-
  Sieve/AddOneCancel.lean
  Generic cancel lemmas for adding/subtracting 1 in additive groups with 1.
  Handy in ZMod proofs (e.g. turn `x + 1 = 1` into `x = 0`).
-/
import Mathlib

noncomputable section
open Classical

namespace Sieve.AddOneCancel

/-- In any additive group with `1`, `x + 1 = 1` iff `x = 0`. -/
lemma add_one_eq_one_iff {R} [AddGroup R] [One R] (x : R) :
    x + (1 : R) = 1 ↔ x = 0 := by
  constructor
  · intro h
    -- add `-1` to both sides
    have h' := congrArg (fun y : R => y + (-1 : R)) h
    -- `(x + 1) + (-1) = 1 + (-1)`  ⇒  `x = 0`
    simp [add_assoc] at h'
    exact h'
  · intro hx; simp [hx]

/-- Symmetric version: `1 + x = 1` iff `x = 0`. -/
lemma one_add_eq_one_iff {R} [AddGroup R] [One R] (x : R) :
    (1 : R) + x = 1 ↔ x = 0 := by
  constructor
  · intro h
    -- commute to the previous lemma
    have := (add_one_eq_one_iff (x := x)).1 (by simpa [add_comm] using h)
    exact this
  · intro hx
    have := (add_one_eq_one_iff (x := x)).2 hx
    simpa [add_comm] using this

/-- If `(1 : R) ≠ 0`, then `(-1 : R) ≠ 0`. (Useful to avoid `NeZero 1` synthesis.) -/
lemma neg_one_ne_zero_of_one_ne_zero {R} [AddGroup R] [One R]
    (h : (1 : R) ≠ 0) : (-1 : R) ≠ 0 := by
  intro hneg
  -- If `-1 = 0` then adding `1` gives `0 = 1`.
  have h01 : (0 : R) = (1 : R) := by
    have t := congrArg (fun y : R => y + (1 : R)) hneg
    simp at t
    exact t
  exact h h01.symm

end Sieve.AddOneCancel
