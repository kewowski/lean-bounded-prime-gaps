import Mathlib
import MaynardTao.Admissible

/-!
MaynardTao/AdmissibleTransforms.lean
------------------------------------
Translation lemmas moved to a separate namespace to avoid name clashes with
`AdmissibleTuples`.
-/

namespace MaynardTao
namespace AdmissibleTransforms

open scoped BigOperators

/-- Translate a finite set of shifts by `t`. -/
def translateSet (t : ℤ) (H : Finset ℤ) : Finset ℤ :=
  H.image (fun h => h + t)

@[simp] lemma translateSet_empty (t : ℤ) : translateSet t (∅ : Finset ℤ) = ∅ := by
  classical
  simp [translateSet]

@[simp] lemma translateSet_singleton (t a : ℤ) :
    translateSet t ({a} : Finset ℤ) = {a + t} := by
  classical
  simp [translateSet]

@[simp] lemma mem_translateSet {t : ℤ} {H : Finset ℤ} {x : ℤ} :
    x ∈ translateSet t H ↔ ∃ h ∈ H, h + t = x := by
  classical
  unfold translateSet
  constructor
  · intro hx
    rcases Finset.mem_image.1 hx with ⟨h, hh, rfl⟩
    exact ⟨h, hh, rfl⟩
  · intro hx
    rcases hx with ⟨h, hh, hx⟩
    subst hx
    exact Finset.mem_image.2 ⟨h, hh, rfl⟩

/-- Residues of a translated set are residues translated in `ZMod p`. -/
lemma residuesMod_translateSet (H : Finset ℤ) (t : ℤ) (p : ℕ) :
    Admissible.residuesMod (translateSet t H) p
      = (Admissible.residuesMod H p).image (fun z : ZMod p => z + (t : ZMod p)) := by
  classical
  ext z; constructor
  · intro hz
    rcases (Admissible.residuesMod_mem (H := translateSet t H) (p := p)).1 hz with ⟨h, hh, hz'⟩
    rcases (mem_translateSet).1 hh with ⟨h0, hh0, rfl⟩
    refine Finset.mem_image.2 ?_
    refine ⟨((h0 : ℤ) : ZMod p), ?_, ?_⟩
    · exact (Admissible.residuesMod_mem (H := H) (p := p)).2 ⟨h0, hh0, rfl⟩
    · simpa [Int.cast_add] using hz'
  · intro hz
    rcases Finset.mem_image.1 hz with ⟨z0, hz0, hz'⟩
    rcases (Admissible.residuesMod_mem (H := H) (p := p)).1 hz0 with ⟨h0, hh0, rfl⟩
    have : ((h0 + t : ℤ) : ZMod p) = z := by
      simpa [Int.cast_add] using hz'
    refine (Admissible.residuesMod_mem (H := translateSet t H) (p := p)).2 ?_
    refine ⟨h0 + t, ?_, this⟩
    exact (mem_translateSet).2 ⟨h0, hh0, rfl⟩

/-- Any singleton set is admissible. -/
lemma admissible_singleton (t : ℤ) : Admissible.IsAdmissible ({t} : Finset ℤ) := by
  intro p hp
  classical
  have hcard : (Admissible.residuesMod ({t} : Finset ℤ) p).card = 1 := by
    simp [Admissible.residuesMod]
  simpa [hcard] using hp.one_lt

/-- Translation preserves admissibility. -/
lemma admissible_translate {H : Finset ℤ} (hAdm : Admissible.IsAdmissible H) (t : ℤ) :
    Admissible.IsAdmissible (translateSet t H) := by
  intro p hp
  classical
  have hleft := residuesMod_translateSet (H := H) (t := t) (p := p)
  have hinjOn :
      Set.InjOn (fun z : ZMod p => z + (t : ZMod p)) ((Admissible.residuesMod H p).toSet) := by
    intro x hx y hy hxy
    simpa using add_right_cancel hxy
  have hcard :
      (Admissible.residuesMod (translateSet t H) p).card
        = (Admissible.residuesMod H p).card := by
    have := (Finset.card_image_iff
      (s := Admissible.residuesMod H p)
      (f := fun z : ZMod p => z + (t : ZMod p))).mpr hinjOn
    simpa [hleft] using this
  simpa [hcard] using (hAdm p hp)

end AdmissibleTransforms
end MaynardTao
