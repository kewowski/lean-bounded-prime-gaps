/-
Sieve/Analytic/BVToolboxSpec.lean
UTF-8 (no BOM).

Leaf module: type-only signatures for the BV analytic toolbox used by Stage-2/3.
This file introduces small, composable structures with typed inequality shapes
but no heavy proofs. It stays Prop-light and avoids importing hubs.

Safe to import anywhere; does not depend on Stage-2/3 or export hubs.
-/
import Mathlib

noncomputable section
open Classical BigOperators
open scoped BigOperators

namespace Sieve
namespace Analytic

/--
LargeSieveProgressions encodes the shape of a large-sieve inequality over
arithmetic progressions modulo q for finitely supported sequences on 0..N.

Bound shape (type only):

∑{r=0}^{q-1} ( ∑{0 ≤ n ≤ N, n ≡ r [q]} a n )^2
≤ LS * ∑_{0 ≤ n ≤ N} (a n)^2

All quantities live in ℝ. Support restriction is encoded by the hypothesis
∀ n, N < n → a n = 0.
-/
structure LargeSieveProgressions where
/-- Modulus (strictly positive). -/
q : ℕ
/-- Summation height (inclusive cutoff uses range (N+1)). -/
N : ℕ
/-- Proof that q ≥ 1 (needed for % q). -/
hq_pos : 0 < q
/-- A numerical large-sieve constant. -/
LS : ℝ
/--
Large-sieve bound signature. No proof is provided here; concrete toolboxes
will populate this field.
-/
bound :
∀ (a : ℕ → ℝ),
(∀ n, N < n → a n = 0) →
(∑ r ∈ Finset.range q,
(∑ n ∈ (Finset.range (N + 1)).filter (fun n => n % q = r), a n) ^ 2)
≤ LS * (∑ n ∈ Finset.range (N + 1), (a n) ^ 2)

/--
OrthogonalityIdentity captures a discrete orthogonality identity over a full
residue system modulo q, expressed in a simple indicator form.

Statement shape (type only):

For 0 ≤ r < q:
∑{n=0}^{q-1} 1{n ≡ r [q]} = 1

in ℝ. (Future variants may generalize to characters.)
-/
structure OrthogonalityIdentity where
q : ℕ
hq_pos : 0 < q
statement :
∀ (r : ℕ), r < q →
(∑ n ∈ Finset.range q, (if n % q = r then (1 : ℝ) else 0)) = 1

/--
PartialSummationBound records a useful discrete partial summation corollary
shape connecting a cumulative function A with its discrete derivative a.

Bound shape (type only, one convenient form):

If A(n+1) - A(n) = a(n) for all n, then

∑_{n=0}^{N} A(n)
  ≤ A(N+1) * (N+1)
    + ∑_{n=0}^{N} |a(n)| * (N+1 - n)


The precise constants are not important here; this is a fast, schematic ledger
that later files can tighten or adjust. Everything is in ℝ.
-/
structure PartialSummationBound where
N : ℕ
bound :
∀ (a A : ℕ → ℝ),
(∀ n, A (n + 1) - A n = a n) →
(∑ n ∈ Finset.range (N + 1), A n)
≤ (A (N + 1) * ((N + 1 : ℕ) : ℝ))
+ (∑ n ∈ Finset.range (N + 1), |a n| * (((N + 1 - n : ℕ) : ℝ)))

/--
BVToolbox is the typed bundle Stage-2/3 consumes. Each field is independently
verifiable and can be discharged in tiny steps (orthogonality → partial summation
→ large sieve), keeping the build green at every step.
-/
structure BVToolbox where
ls : LargeSieveProgressions
ortho : OrthogonalityIdentity
ps : PartialSummationBound

end Analytic
end Sieve
