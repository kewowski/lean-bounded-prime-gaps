/-
  Sieve/AdmissibleTuples.lean
  UTF-8 (no BOM), ASCII-only.
-/
import Mathlib

noncomputable section
open Classical

namespace Sieve.AdmissibleTuples

/-- For a finite set `H` of integer shifts, the image in `ZMod p` is *surjective*
    if every residue class is hit by some `h ∈ H`. -/
def coversAllResiduesMod (H : Finset ℤ) (p : ℕ) : Prop :=
  ∀ x : ZMod p, ∃ h ∈ H, ((h : ZMod p) = x)

/-- An admissible tuple avoids covering all residues modulo every prime. -/
def Admissible (H : Finset ℤ) : Prop :=
  ∀ p : ℕ, p.Prime → ¬ coversAllResiduesMod H p

/-- Translate a tuple by `t`. Definition only; lemmas can come later. -/
def translate (H : Finset ℤ) (t : ℤ) : Finset ℤ :=
  H.image (fun (h : ℤ) => h + t)

section lemmas

/-- Coverage is invariant under translation: covering with `H + t` is equivalent to
    covering with `H`. This is purely algebraic (add/cancel in `ZMod p`). -/
lemma covers_translate_iff (H : Finset ℤ) (t : ℤ) (p : ℕ) :
    coversAllResiduesMod (translate H t) p ↔ coversAllResiduesMod H p := by
  classical
  constructor
  · -- from translated coverage to original coverage
    intro hcov x
    -- ask for coverage of `x + t` by the translated set, then cancel `+ t`
    have hx := hcov (x + (t : ZMod p))
    rcases hx with ⟨h', h'h, heq⟩
    rcases Finset.mem_image.mp h'h with ⟨h, hH, rfl⟩
    -- heq : ((h + t : ℤ) : ZMod p) = x + t
    -- rewrite and cancel `+ t` on the right
    have : (h : ZMod p) + (t : ZMod p) = x + (t : ZMod p) := by
      simpa [Int.cast_add] using heq
    have h_eq : (h : ZMod p) = x := by
      exact add_right_cancel this
    exact ⟨h, hH, h_eq⟩
  · -- from original coverage to translated coverage
    intro hcov x
    -- ask for coverage of `x - t` by the original set, then add `t`
    have hx := hcov (x - (t : ZMod p))
    rcases hx with ⟨h, hH, heq⟩
    -- witness in the translated set is `h + t`
    refine ⟨h + t, ?_, ?_⟩
    · -- membership in the image
      exact Finset.mem_image.mpr ⟨h, hH, rfl⟩
    · -- equality in ZMod p
      -- add `t` to both sides of `(h : ZMod p) = x - t`
      have := congrArg (fun y : ZMod p => y + (t : ZMod p)) heq
      -- rewrite `((h + t : ℤ) : ZMod p)` and simplify
      simpa [Int.cast_add, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this

/-- Admissibility is translation-invariant. -/
lemma admissible_translate_iff (H : Finset ℤ) (t : ℤ) :
    Admissible (translate H t) ↔ Admissible H := by
  classical
  unfold Admissible
  -- pointwise equivalence on `coversAllResiduesMod` ⇒ admissibility equivalence
  refine forall_congr' ?_
  intro p
  refine forall_congr' ?_
  intro hp
  have := covers_translate_iff H t p
  -- use `not_congr` to transport negation across the iff
  simpa [translate, Admissible, coversAllResiduesMod] using not_congr this

end lemmas

end Sieve.AdmissibleTuples
