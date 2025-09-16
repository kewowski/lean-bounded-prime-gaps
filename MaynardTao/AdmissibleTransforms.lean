import Mathlib
import MaynardTao.Admissible

/-!
MaynardTao/AdmissibleTransforms.lean
------------------------------------
Handy lemmas about the structural admissibility predicate:

* `admissible_singleton`  : any singleton set `{t}` is admissible
* `admissible_translate`  : translation by an integer preserves admissibility
-/

namespace MaynardTao
namespace Admissible

open scoped BigOperators

/-- Translate a finite set of shifts by `t`. -/
def translate (t : ℤ) (H : Finset ℤ) : Finset ℤ :=
  H.image (fun h => h + t)

@[simp] lemma translate_empty (t : ℤ) : translate t (∅ : Finset ℤ) = ∅ := by
  classical
  simp [translate]

@[simp] lemma translate_singleton (t a : ℤ) :
    translate t ({a} : Finset ℤ) = {a + t} := by
  classical
  simp [translate]

@[simp] lemma mem_translate {t : ℤ} {H : Finset ℤ} {x : ℤ} :
    x ∈ translate t H ↔ ∃ h ∈ H, h + t = x := by
  classical
  unfold translate
  constructor
  · intro hx
    rcases Finset.mem_image.1 hx with ⟨h, hh, rfl⟩
    exact ⟨h, hh, rfl⟩
  · intro hx
    rcases hx with ⟨h, hh, hx⟩
    subst hx
    exact Finset.mem_image.2 ⟨h, hh, rfl⟩

/-- Residues of a translated set are just residues translated in `ZMod p`. -/
lemma residuesMod_translate (H : Finset ℤ) (t : ℤ) (p : ℕ) :
    residuesMod (translate t H) p
      = (residuesMod H p).image (fun z : ZMod p => z + (t : ZMod p)) := by
  classical
  ext z; constructor
  · intro hz
    rcases (residuesMod_mem (H := translate t H) (p := p)).1 hz with ⟨h, hh, hz⟩
    rcases (mem_translate).1 hh with ⟨h0, hh0, rfl⟩
    refine Finset.mem_image.2 ?_
    refine ⟨((h0 : ℤ) : ZMod p), ?_, ?_⟩
    · exact (residuesMod_mem (H := H) (p := p)).2 ⟨h0, hh0, rfl⟩
    · simpa [Int.cast_add] using hz
  · intro hz
    rcases Finset.mem_image.1 hz with ⟨z0, hz0, hz⟩
    rcases (residuesMod_mem (H := H) (p := p)).1 hz0 with ⟨h0, hh0, rfl⟩
    -- show `(h0 + t : ℤ)` goes to `z`
    have : ((h0 + t : ℤ) : ZMod p) = z := by
      simpa [Int.cast_add] using hz
    -- wrap back into residues of the translated set
    refine (residuesMod_mem (H := translate t H) (p := p)).2 ?_
    refine ⟨h0 + t, ?_, this⟩
    exact (mem_translate).2 ⟨h0, hh0, rfl⟩

/-- Any singleton set is admissible. -/
lemma admissible_singleton (t : ℤ) : IsAdmissible ({t} : Finset ℤ) := by
  intro p hp
  classical
  have hcard : (residuesMod ({t} : Finset ℤ) p).card = 1 := by
    simp [residuesMod]
  simpa [hcard] using hp.one_lt

/-- Translation preserves admissibility. -/
lemma admissible_translate {H : Finset ℤ} (hAdm : IsAdmissible H) (t : ℤ) :
    IsAdmissible (translate t H) := by
  intro p hp
  classical
  have hleft := residuesMod_translate (H := H) (t := t) (p := p)
  -- addition by a constant in `ZMod p` is injective (hence injective on any subset)
  have hinjOn :
      Set.InjOn (fun z : ZMod p => z + (t : ZMod p)) ((residuesMod H p).toSet) := by
    intro x hx y hy hxy
    simpa using add_right_cancel hxy
  have hcard :
      (residuesMod (translate t H) p).card = (residuesMod H p).card := by
    have := (Finset.card_image_iff
      (s := residuesMod H p)
      (f := fun z : ZMod p => z + (t : ZMod p))).mpr hinjOn
    simpa [hleft]
      using this
  simpa [hcard] using (hAdm p hp)

end Admissible
end MaynardTao
