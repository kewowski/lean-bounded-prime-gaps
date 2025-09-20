/-
  Sieve/ZModDemos.lean
  Handy ZMod facts using the generic add-±1 cancel lemmas.
-/
import Mathlib
import Sieve.AddOneCancel

noncomputable section
open Classical

namespace Sieve.ZModDemos

/-- In any `ZMod p`, `x + 1 = 1 ↔ x = 0`. This is just the generic lemma. -/
@[simp] lemma add_one_eq_one_iff {p : ℕ} (x : ZMod p) :
    x + (1 : ZMod p) = 1 ↔ x = 0 :=
  Sieve.AddOneCancel.add_one_eq_one_iff x

/-- For prime `p`, we have `(-1 : ZMod p) ≠ 0`. -/
lemma neg_one_ne_zero_of_prime {p : ℕ} (hp : p.Prime) :
    ((-1 : ZMod p) ≠ 0) := by
  -- ensure `ZMod p` is nontrivial so `zero_ne_one` is available
  haveI : Fact (1 < p) := ⟨hp.one_lt⟩
  intro h
  -- add 1 to both sides; deduce 0 = 1, contradiction
  have h01 : (0 : ZMod p) = 1 := by
    have := congrArg (fun y : ZMod p => (1 : ZMod p) + y) h
    simpa using this.symm
  exact (zero_ne_one : (0 : ZMod p) ≠ 1) h01

end Sieve.ZModDemos
