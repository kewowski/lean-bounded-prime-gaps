import Mathlib
import Sieve.Stage3PrimeFacade
import Sieve.Stage3PrimesEndToEnd
import Sieve.AnalyticBridge

set_option linter.unnecessarySimpa false


open Finset
open scoped BigOperators

/-
  Sieve/Stage3TwinGap.lean
  Minimal, robust version:
  • indicator sum ↔ filtered-cardinality (set-builder form),
  • twin-window ↔ twin primes,
  • Nat→Real bridge for prime façade,
  • analytic-lower-bound witness.
-/

noncomputable section
open Classical

namespace Sieve.Stage3TwinGap

/-! ## Indicator sum = filtered-cardinality (set-builder) -/

/-- For any hit system, the sum of indicators on a window equals the (real) cardinality
    of the filtered window. -/
lemma windowHitCount_eq_card_filter
  (HS : Sieve.Stage3.HitSystem) (H : Finset ℤ) (n : ℤ) :
  Sieve.Stage3.windowHitCount H HS n
    = ((H.filter (fun h => HS.isHit (n + h))).card : ℝ) := by
  classical
  have h1 :
      ∑ h ∈ H, (if HS.isHit (n + h) then (1:ℝ) else 0)
        = ∑ h ∈ H.filter (fun h => HS.isHit (n + h)), (1:ℝ) := by
    simpa using
      (Finset.sum_filter (s:=H) (p:=fun h => HS.isHit (n + h))
                         (f:=fun _ => (1:ℝ))).symm
  have h2 :
      ∑ h ∈ H.filter (fun h => HS.isHit (n + h)), (1:ℝ)
        = ((H.filter (fun h => HS.isHit (n + h))).card : ℝ) := by
    simpa [nsmul_one] using
      (Finset.sum_const (b:=(1:ℝ)) (s:=H.filter (fun h => HS.isHit (n + h))))
  calc
    Sieve.Stage3.windowHitCount H HS n
        = ∑ h ∈ H, Sieve.Stage3.hitIndicator HS (n + h) := by
            simp [Sieve.Stage3.windowHitCount, Sieve.Stage3.windowSum]
    _   = ∑ h ∈ H, (if HS.isHit (n + h) then (1:ℝ) else 0) := by
            simp [Sieve.Stage3.hitIndicator]
    _   = ∑ h ∈ H.filter (fun h => HS.isHit (n + h)), (1:ℝ) := h1
    _   = ((H.filter (fun h => HS.isHit (n + h))).card : ℝ) := h2

/-! ## Twin-window and primality on {0,2} -/

@[simp] private lemma mem_pair (x : ℤ) :
    x ∈ (([0, 2] : List ℤ).toFinset) ↔ x = 0 ∨ x = 2 := by
  simp

/-- If the filtered twin window at `n` has card ≥ 2, then `n` and `n+2` are both prime. -/
theorem twin_window_card_ge_two_imp_twin_primes_pair
    (n : ℤ)
    (h :
      2 ≤ ((([0, 2] : List ℤ).toFinset).filter (fun h => Sieve.Stage3.isPrimeZ (n + h))).card) :
    (Sieve.Stage3.isPrimeZ n ∧ Sieve.Stage3.isPrimeZ (n + 2)) := by
  classical
  let H : Finset ℤ := (([0, 2] : List ℤ).toFinset)
  let S : Finset ℤ := H.filter (fun h => Sieve.Stage3.isPrimeZ (n + h))
  -- `S.card ≤ 2` since `S ⊆ H` and `H.card = 2`
  have hle2 : S.card ≤ 2 := by
    have := (Finset.card_filter_le (s:=H) (p:=fun h => Sieve.Stage3.isPrimeZ (n + h)))
    simpa [H] using this
  -- From `2 ≤ S.card ≤ 2`, get equality.
  have hEq : S.card = 2 := Nat.le_antisymm hle2 h
  -- Show 0 ∈ S, else force S ⊆ {2} and contradict card = 2.
  have h0 : 0 ∈ S := by
    by_contra h0not
    have hSub2 : S ⊆ ({2} : Finset ℤ) := by
      intro x hxS
      have hxH : x ∈ H := (Finset.mem_filter.mp hxS).1
      rcases (by simpa [H] using hxH) with hx0 | hx2
      · exact (False.elim (h0not (by simpa [S, H, hx0] using hxS)))
      · simpa [hx2]
    by_cases h2in : 2 ∈ S
    · have hS_eq : S = ({2} : Finset ℤ) := by
        apply Finset.Subset.antisymm hSub2
        intro x hx; have hx2 : x = 2 := by simpa [Finset.mem_singleton] using hx
        simpa [hx2] using h2in
      have hScard1 : S.card = 1 := by simpa [hS_eq]
      have : 2 ≤ 1 := by simpa [hScard1] using (by simpa [hEq] : 2 ≤ S.card)
      exact (by decide : ¬ (2 ≤ 1)) this
    · have hS_eq : S = (∅ : Finset ℤ) := by
        ext x; constructor
        · intro hx; have := hSub2 hx
          have hx2 : x = 2 := by simpa [Finset.mem_singleton] using this
          exact (h2in (by simpa [hx2] using hx)).elim
        · intro hx; simpa using hx
      have hScard0 : S.card = 0 := by simpa [hS_eq]
      have : 2 ≤ 0 := by simpa [hScard0] using (by simpa [hEq] : 2 ≤ S.card)
      exact (by decide : ¬ (2 ≤ 0)) this
  -- Show 2 ∈ S, symmetrically.
  have h2' : 2 ∈ S := by
    by_contra h2not
    have hSub0 : S ⊆ ({0} : Finset ℤ) := by
      intro x hxS
      have hxH : x ∈ H := (Finset.mem_filter.mp hxS).1
      rcases (by simpa [H] using hxH) with hx0 | hx2
      · simpa [Finset.mem_singleton, hx0]
      · exact (False.elim (h2not (by simpa [S, H, hx2] using hxS)))
    by_cases h0in : 0 ∈ S
    · have hS_eq : S = ({0} : Finset ℤ) := by
        apply Finset.Subset.antisymm hSub0
        intro x hx; have hx0 : x = 0 := by simpa [Finset.mem_singleton] using hx
        simpa [hx0] using h0in
      have hScard1 : S.card = 1 := by simpa [hS_eq]
      have : 2 ≤ 1 := by simpa [hScard1] using (by simpa [hEq] : 2 ≤ S.card)
      exact (by decide : ¬ (2 ≤ 1)) this
    · have hS_eq : S = (∅ : Finset ℤ) := by
        ext x; constructor
        · intro hx; have := hSub0 hx
          have hx0 : x = 0 := by simpa [Finset.mem_singleton] using this
          exact (h0in (by simpa [hx0] using hx)).elim
        · intro hx; simpa using hx
      have hScard0 : S.card = 0 := by simpa [hS_eq]
      have : 2 ≤ 0 := by simpa [hScard0] using (by simpa [hEq] : 2 ≤ S.card)
      exact (by decide : ¬ (2 ≤ 0)) this
  -- Read primes off the filter memberships.
  have hp0 : Sieve.Stage3.isPrimeZ (n + 0) := (Finset.mem_filter.mp h0).2
  have hp2 : Sieve.Stage3.isPrimeZ (n + 2) := (Finset.mem_filter.mp h2').2
  exact ⟨by simpa using hp0, hp2⟩

/-- If `n` and `n+2` are prime, the filtered twin window at `n` has card = 2. -/
theorem twin_primes_imp_twin_window_card_eq_two
    (n : ℤ)
    (hp0 : Sieve.Stage3.isPrimeZ n)
    (hp2 : Sieve.Stage3.isPrimeZ (n + 2)) :
    ((([0, 2] : List ℤ).toFinset).filter (fun h => Sieve.Stage3.isPrimeZ (n + h))).card = 2 := by
  classical
  let H : Finset ℤ := (([0, 2] : List ℤ).toFinset)
  let S : Finset ℤ := H.filter (fun h => Sieve.Stage3.isPrimeZ (n + h))
  have h0 : 0 ∈ S := by
    have : 0 ∈ H := by simp [H]
    exact Finset.mem_filter.mpr ⟨this, by simpa using hp0⟩
  have h2 : 2 ∈ S := by
    have : 2 ∈ H := by simp [H]
    exact Finset.mem_filter.mpr ⟨this, by simpa using hp2⟩
  -- S ⊆ H and contains both 0 and 2, hence S = H, so card = 2.
  have SsubH : S ⊆ H := by intro x hx; exact (Finset.mem_filter.mp hx).1
  have HsubS : H ⊆ S := by
    intro x hxH
    rcases (by simpa [H] using hxH) with hx0 | hx2
    · simpa [hx0] using h0
    · simpa [hx2] using h2
  have S_eq : S = H := by exact Finset.Subset.antisymm SsubH HsubS
  -- Conclude card S = 2, then rewrite back to the goal form.
  have ScardEq : S.card = 2 := by
    have : S.card = H.card := by simpa [S_eq]
    simpa [H] using this
  simpa [S, H] using ScardEq

/-- On the twin window `{0,2}`, having exactly two prime hits is equivalent
    to `n` and `n+2` both being prime. -/
theorem twin_window_card_eq_two_iff_twin_primes
    (n : ℤ) :
    ((([0, 2] : List ℤ).toFinset).filter (fun h => Sieve.Stage3.isPrimeZ (n + h))).card = 2
    ↔ (Sieve.Stage3.isPrimeZ n ∧ Sieve.Stage3.isPrimeZ (n + 2)) := by
  classical
  constructor
  · intro hEq
    -- Bridge list ↔ set for the filtered window to avoid simpa/assumption fragility.
    have pair_eq :
      ((([0, 2] : List ℤ).toFinset).filter (fun h => Sieve.Stage3.isPrimeZ (n + h)))
      =
      (({0, 2} : Finset ℤ).filter (fun h => Sieve.Stage3.isPrimeZ (n + h))) := by
      ext x; simp
    have hEqSet :
      ((({0, 2} : Finset ℤ).filter (fun h => Sieve.Stage3.isPrimeZ (n + h))).card) = 2 := by
      simpa [pair_eq] using hEq
    have hge :
      2 ≤ ((([0, 2] : List ℤ).toFinset).filter (fun h => Sieve.Stage3.isPrimeZ (n + h))).card := by
      have hgeSet :
        2 ≤ ((({0, 2} : Finset ℤ).filter (fun h => Sieve.Stage3.isPrimeZ (n + h))).card) := by
        simpa [hEqSet]
      simpa [pair_eq] using hgeSet
    exact twin_window_card_ge_two_imp_twin_primes_pair n hge
  · intro hpr
    exact twin_primes_imp_twin_window_card_eq_two n hpr.1 hpr.2

/-! ## Nat-card ≥ 2 ⇒ Real windowHitCount ≥ 2 (prime façade) -/

/-- Convert a *natural* `card ≥ 2` on the twin window to a *real* `windowHitCount ≥ 2`
    for the prime façade. -/
lemma twinWindow_natCard_ge_two_implies_windowCount_ge_two
  (cfg : Sieve.MTCore.TupleConfig) (n : ℤ) :
  (2 : ℕ) ≤ ((([0, 2] : List ℤ).toFinset).filter (fun h => Sieve.Stage3.isPrimeZ (n + h))).card →
  (2 : ℝ) ≤
    Sieve.Stage3.windowHitCount (([0, 2] : List ℤ).toFinset) (Sieve.Stage3.primeHS cfg) n := by
  classical
  let H : Finset ℤ := (([0, 2] : List ℤ).toFinset)
  intro hk
  -- Cast Nat ≤ card to Real, then rewrite via indicator ↔ card lemma.
  have hkReal :
      (2 : ℝ) ≤ ((H.filter (fun h => Sieve.Stage3.isPrimeZ (n + h))).card : ℝ) := by
    exact_mod_cast hk
  have hcount :
    Sieve.Stage3.windowHitCount H (Sieve.Stage3.primeHS cfg) n
      = ((H.filter (fun h => Sieve.Stage3.isPrimeZ (n + h))).card : ℝ) := by
    simpa [Sieve.Stage3.primeHS] using
      windowHitCount_eq_card_filter (HS := Sieve.Stage3.primeHS cfg) (H := H) (n := n)
  have hList :
      (2 : ℝ) ≤ Sieve.Stage3.windowHitCount H (Sieve.Stage3.primeHS cfg) n := by
    simpa [hcount] using hkReal
  have Hpair : H = ({0, 2} : Finset ℤ) := by
    ext x; simp [H]
  simpa [Hpair] using hList
/-! ## AI lower bound ⇒ witness with twin-window count ≥ 2 -/

/-- From an analytic lower bound `AI.lower ≥ 2` for the twin window and the prime façade,
    together with `avg ≥ τ` (to witness heavy-set nonemptiness), produce `n` where the twin
    window count is at least `2`. -/
theorem exists_twin_window_with_two_primes_of_AI_ge_two_from_avg
  (AI : Sieve.Analytic.AvgWindowHitLB)
  (W  : Sieve.MaynardWeights.Weight) (τ : ℝ)
  (cfg : Sieve.MTCore.TupleConfig)
  (hpos   : 0 < W.support.card)
  (hτleavg : τ ≤ (∑ m ∈ W.support, W.w m) / (W.support.card : ℝ))
  (h2  :
    (2 : ℝ) ≤
      AI.lower W τ (([0, 2] : List ℤ).toFinset) (Sieve.Stage3.primeHS cfg)
        (Sieve.Stage3.heavySet_nonempty_of_avg_ge (W := W) (τ := τ) hpos hτleavg)) :
  ∃ n : ℤ,
    2 ≤
      Sieve.Stage3.windowHitCount (([0, 2] : List ℤ).toFinset)
        (Sieve.Stage3.primeHS cfg) n := by
  classical
  obtain ⟨n, _hne, hk⟩ :=
    Sieve.Stage3.exists_atLeast_k_primes_in_twin_window_of_AI_ge_k_from_avg
      (AI := AI) (W := W) (τ := τ) (cfg := cfg)
      (hpos := hpos) (hτleavg := hτleavg) (k := 2) (hk := h2)
  exact ⟨n, twinWindow_natCard_ge_two_implies_windowCount_ge_two (cfg := cfg) (n := n) (by simpa using hk)⟩

end Sieve.Stage3TwinGap

