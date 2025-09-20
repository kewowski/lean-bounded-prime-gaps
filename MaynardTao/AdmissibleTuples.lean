import Mathlib

/-!
MaynardTao/AdmissibleTuples.lean
--------------------------------
Dependency-light definitions and lemmas for admissible k-tuples.

* `isAdmissible H` : for every prime `p`, there exists `a : ZMod p`
  with `a + h ≠ 0` for all `h ∈ H`.
* `translate H t` : shift by `t : ℤ`. Admissibility is translation-invariant.
-/

namespace MaynardTao

/-- A finite set `H : Finset ℤ` is admissible if, for every prime `p`,
there is a residue class `a : ZMod p` that avoids all `-h (mod p)` for `h ∈ H`. -/
def isAdmissible (H : Finset ℤ) : Prop :=
  ∀ p : ℕ, Nat.Prime p → ∃ a : ZMod p, ∀ h ∈ H, a + (h : ZMod p) ≠ 0

/-- Translate a tuple `H` by `t : ℤ`. -/
def translate (H : Finset ℤ) (t : ℤ) : Finset ℤ :=
  H.image (fun h => h + t)

namespace Admissible

@[simp] lemma translate_empty (t : ℤ) : translate (∅ : Finset ℤ) t = ∅ := by
  simp [translate]

lemma isAdmissible_empty : isAdmissible (∅ : Finset ℤ) := by
  intro p hp
  refine ⟨(0 : ZMod p), ?_⟩
  intro _ hh
  -- membership in the empty finset is impossible
  simp at hh

lemma isAdmissible_of_subset {H₁ H₂ : Finset ℤ}
    (hsub : H₁ ⊆ H₂) (h₂ : isAdmissible H₂) : isAdmissible H₁ := by
  intro p hp
  rcases h₂ p hp with ⟨a, ha⟩
  refine ⟨a, ?_⟩
  intro h hh1
  exact ha h (hsub hh1)

/-- Admissibility is invariant under translation by any `t : ℤ`. -/
lemma isAdmissible_translate_iff (H : Finset ℤ) (t : ℤ) :
    isAdmissible (translate H t) ↔ isAdmissible H := by
  constructor
  · -- If `translate H t` is admissible, then `H` is admissible.
    intro hTrans p hp
    rcases hTrans p hp with ⟨a, ha⟩
    -- witness for `H`: a + t
    refine ⟨a + (t : ZMod p), ?_⟩
    intro h hh
    -- show `h + t ∈ translate H t`
    have hx : (h + t) ∈ translate H t := by
      refine Finset.mem_image.mpr ?_
      exact ⟨h, hh, rfl⟩
    -- specialize `ha` at `x = h + t`
    have : a + ((h + t : ℤ) : ZMod p) ≠ 0 := ha (h + t) hx
    -- `(h + t : ℤ)` casts as `(h : ZMod p) + (t : ZMod p)`
    simpa [Int.cast_add, add_assoc, add_left_comm, add_comm] using this
  · -- If `H` is admissible, then `translate H t` is admissible.
    intro hH p hp
    rcases hH p hp with ⟨a, ha⟩
    -- witness for `translate H t`: a - t
    refine ⟨a - (t : ZMod p), ?_⟩
    intro x hx
    -- unpack membership in the image to get `x = h + t` for some `h ∈ H`
    rcases Finset.mem_image.mp hx with ⟨h, hh, rfl⟩
    -- from `ha` we know `a + h ≠ 0`
    have : a + (h : ZMod p) ≠ 0 := ha h hh
    -- rewrite `(a - t) + (h + t)` to `a + h`
    simpa [sub_eq_add_neg, Int.cast_add, Int.cast_neg, add_assoc, add_left_comm, add_comm]
      using this

end Admissible

end MaynardTao
