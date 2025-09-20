/-
  Sieve/AdmissiblePairEven.lean
  General twin-style admissibility: {0,d} is admissible when d = 2*t.
-/
import Mathlib
import Sieve.AdmissibleTuples

noncomputable section
open Classical

namespace Sieve.AdmissiblePairEven
open Sieve.AdmissibleTuples

/-- The 2-point tuple `{0,d}`. -/
def pair (d : ℤ) : Finset ℤ := ({0, d} : Finset ℤ)

/-- If `d = 2 * t` then `{0, d}` is admissible.  (Covers the twin case with `t = 1`.) -/
lemma admissible_pair_of_even (d t : ℤ) (hd : d = 2 * t) :
    Admissible (pair d) := by
  classical
  -- Prove for the translate by `-t` (which becomes `{ -t, t }`), then pull back.
  have h' : Admissible (translate (pair d) (-t)) := by
    unfold Admissible
    intro p hp hcov
    -- ZMod p is nontrivial; get `0 ≠ 1`.
    haveI : Fact (1 < p) := ⟨hp.one_lt⟩
    set T : ZMod p := (t : ZMod p)

    -- Case split on T.
    by_cases hT : T = 0
    · -- If T = 0, show residue 1 is not hit.
      obtain ⟨h, hh, heq⟩ := hcov (1 : ZMod p)
      rcases Finset.mem_image.mp hh with ⟨h0, h0mem, rfl⟩
      -- h = h0 - t, with h0 ∈ {0, d}.
      rcases Finset.mem_insert.mp h0mem with rfl | hdmem
      · -- h0 = 0 ⇒ (-t : ZMod p) = 1 ⇒ 0 = 1 (since T = 0).
        have : (-(T)) = (1 : ZMod p) := by
          simpa [Int.cast_add, Int.cast_neg, sub_eq_add_neg] using heq
        have : (0 : ZMod p) = 1 := by simpa [hT] using this
        exact (zero_ne_one : (0 : ZMod p) ≠ 1) this
      · -- h0 = d ⇒ (d - t : ZMod p) = 1. Using d = 2t, this says T = 1.
        have hd0 : h0 = d := by simpa using (Finset.mem_singleton.mp hdmem)
        have : T = (1 : ZMod p) := by
          -- Cast and simplify: (d - t) = 1 ⇒ (2t - t) = 1 ⇒ t = 1.
          have : ((d - t : ℤ) : ZMod p) = (1 : ZMod p) := by
            simpa [Int.cast_add, Int.cast_neg, sub_eq_add_neg, hd0] using heq
          simpa [hd, Int.cast_mul, Int.cast_ofNat, two_mul,
                 sub_eq_add_neg, Int.cast_add, Int.cast_neg] using this
        have : (0 : ZMod p) = (1 : ZMod p) := by simpa [hT] using this
        exact (zero_ne_one : (0 : ZMod p) ≠ 1) this
    · -- If T ≠ 0, show residue 0 is not hit.
      obtain ⟨h, hh, heq0⟩ := hcov (0 : ZMod p)
      rcases Finset.mem_image.mp hh with ⟨h0, h0mem, rfl⟩
      rcases Finset.mem_insert.mp h0mem with rfl | hdmem
      · -- h0 = 0 ⇒ (-t : ZMod p) = 0 ⇒ T = 0, contradiction.
        have : (-(T)) = (0 : ZMod p) := by
          simpa [Int.cast_add, Int.cast_neg, sub_eq_add_neg] using heq0
        have : T = 0 := by
          -- add T to both sides to get `0 = T`
          have := congrArg (fun y : ZMod p => y + T) this
          have : (0 : ZMod p) = T := by
            simpa using this
          simpa using this.symm
        exact hT this
      · -- h0 = d ⇒ (d - t : ZMod p) = 0. With d = 2t, this forces T = 0.
        have hd0 : h0 = d := by simpa using (Finset.mem_singleton.mp hdmem)
        have : ((d - t : ℤ) : ZMod p) = 0 := by
          simpa [Int.cast_add, Int.cast_neg, sub_eq_add_neg, hd0] using heq0
        have : T = 0 := by
          -- From (d - t) = 0 in ZMod p and d = 2t, conclude (t : _) = 0.
          have : ((t : ℤ) : ZMod p) = 0 := by
            simpa [hd, Int.cast_mul, Int.cast_ofNat, two_mul,
                   sub_eq_add_neg, Int.cast_add, Int.cast_neg] using this
          simpa using this
        exact hT this

  -- Pull back along translation invariance.
  exact (admissible_translate_iff (pair d) (-t)).1 h'

/-- Special case: `{0, 2}` is admissible (take `t = 1`). -/
lemma admissible_twin' : Admissible (pair 2) :=
  admissible_pair_of_even 2 1 (by norm_num)

end Sieve.AdmissiblePairEven
