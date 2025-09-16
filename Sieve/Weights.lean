/-
  Sieve/Weights.lean
  UTF-8 (no BOM), ASCII-only.

  Core helpers for the Maynard–Tao scaffold.
  Conventions:
    * indicator indR : Prop -> Real
    * prodShift : finite product of (n + h)
    * supportD : divisors 1..D
    * weight   : sum over supportD D
    * lambdaL2 : sum of abs-squares on a Finset
    * all "split at d0" lemmas are in abs-squares, never plain squares
-/

import Mathlib

open scoped BigOperators
open Classical

namespace Sieve

/-- Real-valued indicator: 1 if p, else 0. -/
def indR (p : Prop) [Decidable p] : Real := if p then (1 : Real) else 0

@[simp] lemma indR_of_true {p : Prop} [Decidable p] (hp : p) : indR p = 1 := by
  simp [indR, hp]

@[simp] lemma indR_of_false {p : Prop} [Decidable p] (hnp : ¬ p) : indR p = 0 := by
  simp [indR, hnp]

/-- Product of shifts (n + h) over a finite set H. -/
def prodShift (H : Finset Nat) (n : Nat) : Nat :=
  H.prod (fun h => n + h)

@[simp] lemma prodShift_empty (n : Nat) : prodShift (∅ : Finset Nat) n = 1 := by
  simp [prodShift]

lemma prodShift_insert {H : Finset Nat} {h : Nat} (hh : h ∉ H) (n : Nat) :
  prodShift (insert h H) n = (n + h) * prodShift H n := by
  classical
  simp [prodShift, hh, mul_comm]

/-- Default support 1..D. -/
def supportD (D : Nat) : Finset Nat := Finset.Icc 1 D

@[simp] lemma supportD_zero : supportD 0 = (∅ : Finset Nat) := by
  simp [supportD]

@[simp] lemma mem_supportD {D d : Nat} :
  d ∈ supportD D ↔ 1 <= d ∧ d <= D := by
  simp [supportD]

/-- Per-n weight. -/
def weight (D : Nat) (lam : Nat -> Real) (H : Finset Nat) (n : Nat) : Real :=
  (supportD D).sum (fun d => lam d * indR (d ∣ prodShift H n))

/-- L2 mass (sum of abs-squares) over a finite set. -/
def lambdaL2 (s : Finset Nat) (lam : Nat -> Real) : Real :=
  s.sum (fun d => (|lam d|) ^ 2)

@[simp] lemma lambdaL2_def (s : Finset Nat) (lam : Nat -> Real) :
  lambdaL2 s lam = s.sum (fun d => (|lam d|) ^ 2) := rfl

/-- If the support is empty, the weight sum is 0. Shaped for `simp [weight, hs]`. -/
lemma sum_supportD_eq_zero_of_empty
  {D : Nat} (h : supportD D = (∅ : Finset Nat))
  (lam : Nat -> Real) (H : Finset Nat) (n : Nat) :
  (supportD D).sum (fun d => lam d * indR (d ∣ prodShift H n)) = 0 := by
  simp [h]

/-! ### Abs-square splitting identities -/

/-- Split the abs-square sum at `d0`. -/
lemma sum_erase_add_absSq
  (s : Finset Nat) (lam : Nat -> Real) {d0 : Nat} (hd0 : d0 ∈ s) :
  (s.erase d0).sum (fun x => (|lam x|) ^ 2) + (|lam d0|) ^ 2
  = s.sum (fun x => (|lam x|) ^ 2) := by
  classical
  -- Use the equality exactly as returned; no `simpa` so there is no drift to plain squares.
  exact Finset.sum_erase_add (s := s) (f := fun x => (|lam x|) ^ 2) hd0

/-- Tail nonnegativity for abs-squares on `s.erase d0`. -/
lemma tail_absSq_nonneg (s : Finset Nat) (lam : Nat -> Real) (d0 : Nat) :
  0 <= (s.erase d0).sum (fun x => (|lam x|) ^ 2) := by
  classical
  -- Each term is a square, hence nonnegative.
  exact Finset.sum_nonneg (by intro x hx; exact sq_nonneg _)

/-- Inequality form after selecting a head element `d0`. -/
lemma head_plus_tail_le_total_absSq
  (s : Finset Nat) (lam : Nat -> Real) {d0 : Nat} (hd0 : d0 ∈ s) :
  (|lam d0|) ^ 2 + (s.erase d0).sum (fun x => (|lam x|) ^ 2)
  <= s.sum (fun x => (|lam x|) ^ 2) := by
  classical
  have hsplit := sum_erase_add_absSq s lam hd0
  -- Commute the sum to match `hsplit`, then conclude by equality.
  have : (|lam d0|) ^ 2 + (s.erase d0).sum (fun x => (|lam x|) ^ 2)
       = (s.erase d0).sum (fun x => (|lam x|) ^ 2) + (|lam d0|) ^ 2 := by
    simp [add_comm]
  exact le_of_eq (this.trans hsplit)

/-- Canonical rewrite: sum of abs-squares equals `lambdaL2`. -/
lemma sum_absSq_to_lambdaL2 (s : Finset Nat) (lam : Nat -> Real) :
  s.sum (fun d => (|lam d|) ^ 2) = lambdaL2 s lam := by
  simp [lambdaL2]

end Sieve

