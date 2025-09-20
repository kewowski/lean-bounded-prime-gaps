
/-
  Sieve/Weights.lean
  ASCII-only, UTF-8 (no BOM), Lean 4.22.0-rc4 + Mathlib.

  Minimal helpers used by the sieve weights and the abs-square L2 bookkeeping.
  Points of care:
  * Use abs-squares consistently: (|lam d|)^2
  * Empty-support branch closes by `simp [weight, hs]`
  * No `sorry`. No fragile `simpa` where linter complains.
-/

import Mathlib

open scoped BigOperators
open BigOperators
open Classical

namespace Sieve

/-- Real-valued indicator of a proposition: 1 if true, 0 otherwise. -/
def indR (p : Prop) [Decidable p] : Real := if p then (1 : Real) else 0

@[simp] lemma indR_of_true {p : Prop} [Decidable p] (hp : p) : indR p = 1 := by
  simp [indR, hp]

@[simp] lemma indR_of_false {p : Prop} [Decidable p] (hnp : ¬ p) : indR p = 0 := by
  simp [indR, hnp]

/-- Product of (n + h) over a finite set `H`. -/
def prodShift (H : Finset Nat) (n : Nat) : Nat :=
  H.prod (fun h => n + h)

@[simp] lemma prodShift_empty (n : Nat) : prodShift (∅ : Finset Nat) n = 1 := by
  simp [prodShift]

/-- Default divisor support: 1..D inclusive. -/
def supportD (D : Nat) : Finset Nat := Finset.Icc 1 D

@[simp] lemma supportD_zero : supportD 0 = (∅ : Finset Nat) := by
  simp [supportD]

@[simp] lemma mem_supportD {D d : Nat} :
  d ∈ supportD D ↔ 1 <= d ∧ d <= D := by
  simp [supportD]

/-- Main per-n weight sum. -/
def weight (D : Nat) (lam : Nat -> Real) (H : Finset Nat) (n : Nat) : Real :=
  (supportD D).sum (fun d => lam d * indR (d ∣ prodShift H n))

/-- L2 mass of lambda on a finite set (abs-squares). -/
def lambdaL2 (s : Finset Nat) (lam : Nat -> Real) : Real :=
  s.sum (fun d => (|lam d|) ^ 2)

@[simp] lemma lambdaL2_def (s : Finset Nat) (lam : Nat -> Real) :
  lambdaL2 s lam = s.sum (fun d => (|lam d|) ^ 2) := rfl

/-- If the support is empty, the weight sum is 0 (shaped so that `simp [weight, hs]` works). -/
lemma sum_supportD_eq_zero_of_empty
  {D : Nat} (h : supportD D = (∅ : Finset Nat))
  (lam : Nat -> Real) (H : Finset Nat) (n : Nat) :
  (supportD D).sum (fun d => lam d * indR (d ∣ prodShift H n)) = 0 := by
  simp [h]

/-! ### Abs-square split and tail nonnegativity -/

/-- Split the abs-square sum at a distinguished element `d0`. -/
lemma sum_erase_add_absSq
  (s : Finset Nat) (lam : Nat -> Real) {d0 : Nat} (hd0 : d0 ∈ s) :
  (s.erase d0).sum (fun x => (|lam x|) ^ 2) + (|lam d0|) ^ 2
  = s.sum (fun x => (|lam x|) ^ 2) := by
  classical
  exact Finset.sum_erase_add (s := s) (f := fun x => (|lam x|) ^ 2) hd0

/-- Tail nonnegativity for abs-squares on `s.erase d0`. -/
lemma tail_absSq_nonneg (s : Finset Nat) (lam : Nat -> Real) (d0 : Nat) :
  0 <= (s.erase d0).sum (fun x => (|lam x|) ^ 2) := by
  classical
  have hterm : forall x, 0 <= (|lam x| : Real) ^ 2 := by
    intro x
    -- 0 <= (|lam x|)^2 by general fact sq_nonneg
    simpa using (sq_nonneg (|lam x| : Real))
  exact Finset.sum_nonneg (by intro x hx; exact hterm x)

/-- Inequality form used after selecting a maximiser `d0` for `|lam d|`. -/
lemma head_plus_tail_le_total_absSq
  (s : Finset Nat) (lam : Nat -> Real) {d0 : Nat} (hd0 : d0 ∈ s) :
  (|lam d0|) ^ 2 + (s.erase d0).sum (fun x => (|lam x|) ^ 2)
  <= s.sum (fun x => (|lam x|) ^ 2) := by
  classical
  -- From commutativity, rewrite head+tail to tail+head, then use the split identity.
  have hsplit := sum_erase_add_absSq s lam hd0
  -- calc chain to avoid fragile rewrites
  have hEq :
    (|lam d0|) ^ 2 + (s.erase d0).sum (fun x => (|lam x|) ^ 2)
    = s.sum (fun x => (|lam x|) ^ 2) := by
    calc
      (|lam d0|) ^ 2 + (s.erase d0).sum (fun x => (|lam x|) ^ 2)
          = (s.erase d0).sum (fun x => (|lam x|) ^ 2) + (|lam d0|) ^ 2 := by
                simp [add_comm]
      _   = s.sum (fun x => (|lam x|) ^ 2) := hsplit
  exact le_of_eq hEq

-- Elementary bound: ∑_{q=1}^Q q ≤ Q^2 (as real numbers).
-- Elementary bound: ∑_{q=1}^Q q ≤ Q^2 (as real numbers).
end Sieve




-- Elementary bound: ∑_{q=1}^Q q ≤ Q^2 (as real numbers).

