import Mathlib
import Sieve.Compat.FinsetCard
import Sieve.Stage3PrimeFacade
import Sieve.Stage3PrimesEndToEnd
import Sieve.AnalyticBridge
import Sieve.Stage3HitCard
set_option linter.unnecessarySimpa false

noncomputable section
open Classical
open Finset
open scoped BigOperators

namespace Sieve.Stage3TwinGap

@[simp] theorem mem_twinList {z : ℤ} :
  z ∈ (([0,2] : List ℤ).toFinset) ↔ z = 0 ∨ z = 2 := by
  simp

@[simp] theorem card_twinList :
  (([0,2] : List ℤ).toFinset).card = 2 := by
  simp

/-- If the filtered twin window at 
 has card ≥ 2, then both 
 and 
+2 are prime. -/
theorem twin_window_card_ge_two_imp_twin_primes_pair
  (n : ℤ)
  (h :
    2 ≤ ((([0,2] : List ℤ).toFinset).filter (fun h => Sieve.Stage3.isPrimeZ (n + h))).card) :
  (Sieve.Stage3.isPrimeZ n ∧ Sieve.Stage3.isPrimeZ (n + 2)) := by
  classical
  let H : Finset ℤ := (([0,2] : List ℤ).toFinset)
  let S : Finset ℤ := H.filter (fun h => Sieve.Stage3.isPrimeZ (n + h))
  have SsubH : S ⊆ H := by
    simpa [S] using (Finset.filter_subset (s := H) (p := fun h => Sieve.Stage3.isPrimeZ (n + h)))
  have S_le_two : S.card ≤ 2 := by
    have := Finset.card_le_of_subset SsubH
    simpa [H] using this
  have hEq2 : S.card = 2 := Nat.le_antisymm S_le_two (by simpa [S, H] using h)
  -- deduce 0 ∈ S
  have h0in : 0 ∈ S := by
    by_contra h0
    have hSub2 : S ⊆ ({2} : Finset ℤ) := by
      intro x hxS
      have hxH : x ∈ H := SsubH hxS
      rcases (by simpa [H] using hxH) with hx0 | hx2
      · exact (False.elim (h0 (by simpa [S, hx0] using hxS)))
      · simpa [hx2]
    have : S.card ≤ ({2} : Finset ℤ).card := Finset.card_le_of_subset hSub2
    have : (2 : ℕ) ≤ 1 := by simpa [hEq2] using this
    exact (by decide : ¬ (2 ≤ 1)) this
  -- deduce 2 ∈ S
  have h2in : 2 ∈ S := by
    by_contra h2
    have hSub0 : S ⊆ ({0} : Finset ℤ) := by
      intro x hxS
      have hxH : x ∈ H := SsubH hxS
      rcases (by simpa [H] using hxH) with hx0 | hx2
      · simpa [hx0]
      · exact (False.elim (h2 (by simpa [S, hx2] using hxS)))
    have : S.card ≤ ({0} : Finset ℤ).card := Finset.card_le_of_subset hSub0
    have : (2 : ℕ) ≤ 1 := by simpa [hEq2] using this
    exact (by decide : ¬ (2 ≤ 1)) this
  have hp0 : Sieve.Stage3.isPrimeZ (n + 0) := (Finset.mem_filter.mp h0in).2
  have hp2 : Sieve.Stage3.isPrimeZ (n + 2) := (Finset.mem_filter.mp h2in).2
  exact ⟨by simpa using hp0, hp2⟩

/-- If both 
 and 
+2 are prime then the filtered twin window has card = 2. -/
theorem twin_primes_imp_twin_window_card_eq_two
  (n : ℤ)
  (hp0 : Sieve.Stage3.isPrimeZ n)
  (hp2 : Sieve.Stage3.isPrimeZ (n + 2)) :
  ((([0,2] : List ℤ).toFinset).filter (fun h => Sieve.Stage3.isPrimeZ (n + h))).card = 2 := by
  classical
  let H : Finset ℤ := (([0,2] : List ℤ).toFinset)
  let S : Finset ℤ := H.filter (fun h => Sieve.Stage3.isPrimeZ (n + h))
  have h0 : 0 ∈ S := by
    have : 0 ∈ H := by simp [H]
    exact Finset.mem_filter.mpr ⟨this, by simpa using hp0⟩
  have h2 : 2 ∈ S := by
    have : 2 ∈ H := by simp [H]
    exact Finset.mem_filter.mpr ⟨this, by simpa using hp2⟩
  have SsubPair : S ⊆ ({0,2} : Finset ℤ) := by
    intro x hxS
    have hxH : x ∈ H := (Finset.mem_filter.mp hxS).1
    simpa [H] using hxH
  have S_eq : S = ({0,2} : Finset ℤ) := by
    apply Finset.Subset.antisymm SsubPair
    intro x hx
    rcases (by simpa [Finset.mem_insert, Finset.mem_singleton] using hx) with hx0 | hx2
    · simpa [S, H, hx0] using h0
    · simpa [S, H, hx2] using h2
  have : ({h ∈ H | Sieve.Stage3.isPrimeZ (n + h)}).card = 2 := by
    simpa [S, S_eq]
  have Hpair : H = ({0,2} : Finset ℤ) := by simp [H]
  simpa [Hpair] using this

/-- Exactly two hits in the twin window ↔ a twin prime pair at shift 
. -/
theorem twin_window_card_eq_two_iff_twin_primes
  (n : ℤ) :
  ((([0,2] : List ℤ).toFinset).filter (fun h => Sieve.Stage3.isPrimeZ (n + h))).card = 2
  ↔ (Sieve.Stage3.isPrimeZ n ∧ Sieve.Stage3.isPrimeZ (n + 2)) := by
  constructor
  · intro hEq
    -- use equality to get 2 ≤ card in the right-hand shape
    have hge :
      2 ≤ ((([0,2] : List ℤ).toFinset).filter (fun h => Sieve.Stage3.isPrimeZ (n + h))).card := by
      simpa using (hEq.symm ▸ (Nat.le_refl (2 : ℕ)))
    exact twin_window_card_ge_two_imp_twin_primes_pair n hge
  · intro hpr
    exact twin_primes_imp_twin_window_card_eq_two n hpr.1 hpr.2

/-- From a Nat ≥ 2 on the filtered twin window to a Real bound on windowHitCount. -/
lemma twinWindow_natCard_ge_two_implies_windowCount_ge_two
  (cfg : Sieve.MTCore.TupleConfig) (n : ℤ) :
  (2 : ℕ) ≤ ((([0,2] : List ℤ).toFinset).filter (fun h => Sieve.Stage3.isPrimeZ (n + h))).card →
  (2 : ℝ) ≤ Sieve.Stage3.windowHitCount (([0,2] : List ℤ).toFinset) (Sieve.Stage3.primeHS cfg) n := by
  classical
  let H : Finset ℤ := (([0,2] : List ℤ).toFinset)
  intro hk
  -- cast Nat inequality to ℝ
  have hkNat :
      (2 : ℕ) ≤ ({x ∈ H | Sieve.Stage3.isPrimeZ (n + x)}).card := by
    simpa [H] using hk
  have hkReal :
      (2 : ℝ) ≤ (({x ∈ H | Sieve.Stage3.isPrimeZ (n + x)}).card : ℝ) := by
    exact_mod_cast hkNat
  -- rewrite windowHitCount to a (real) card
  have hcount :
    Sieve.Stage3.windowHitCount H (Sieve.Stage3.primeHS cfg) n
      = (({x ∈ H | Sieve.Stage3.isPrimeZ (n + x)}).card : ℝ) := by
    simpa [Sieve.Stage3.primeHS] using
      Sieve.Stage3.windowHitCount_eq_card_filter (H := H) (HS := Sieve.Stage3.primeHS cfg) (n := n)
  -- conclude
  have : (2 : ℝ) ≤ Sieve.Stage3.windowHitCount H (Sieve.Stage3.primeHS cfg) n := by
    simpa [hcount] using hkReal
  simpa [H] using this

/-- Using the analytic lower bound to exhibit a point with ≥ 2 hits in the twin window. -/
theorem exists_twin_window_with_two_primes_of_AI_ge_two_from_avg
  (AI : Sieve.Analytic.AvgWindowHitLB)
  (W  : Sieve.MaynardWeights.Weight) (τ : ℝ)
  (cfg : Sieve.MTCore.TupleConfig)
  (hpos   : 0 < W.support.card)
  (hτleavg : τ ≤ (∑ m ∈ W.support, W.w m) / (W.support.card : ℝ))
  (h2  :
    (2 : ℝ) ≤ AI.lower W τ (([0,2] : List ℤ).toFinset) (Sieve.Stage3.primeHS cfg)
      (Sieve.Stage3.heavySet_nonempty_of_avg_ge (W := W) (τ := τ) hpos hτleavg)) :
  ∃ n : ℤ,
    2 ≤ Sieve.Stage3.windowHitCount (([0,2] : List ℤ).toFinset) (Sieve.Stage3.primeHS cfg) n := by
  classical
  obtain ⟨n, _hne, hk⟩ :=
    Sieve.Stage3.exists_atLeast_k_primes_in_twin_window_of_AI_ge_k_from_avg
      (AI := AI) (W := W) (τ := τ) (cfg := cfg)
      (hpos := hpos) (hτleavg := hτleavg) (k := 2) (hk := h2)
  exact ⟨n, twinWindow_natCard_ge_two_implies_windowCount_ge_two (cfg := cfg) (n := n) (by simpa)⟩

end Sieve.Stage3TwinGap





