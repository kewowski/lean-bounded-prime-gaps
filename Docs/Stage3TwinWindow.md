# Stage-3 twin-window façade (H = {0,2})

**What’s provided (robust, minimal proofs):**
- `windowHitCount_eq_card_filter`  
  average of hit indicators over a window = (real) cardinality of the filtered window.

- `twin_window_card_ge_two_imp_twin_primes_pair`  
  if `#{h∈{0,2} | isPrimeZ (n+h)} ≥ 2` then `isPrimeZ n ∧ isPrimeZ (n+2)`.

- `twin_primes_imp_twin_window_card_eq_two`  
  if `isPrimeZ n ∧ isPrimeZ (n+2)` then the filtered twin window has card `2`.

- `twin_window_card_eq_two_iff_twin_primes`  
  equivalence: card = 2 ↔ primes at `n` and `n+2`.

- `twinWindow_natCard_ge_two_implies_windowCount_ge_two`  
  Nat→Real bridge for prime façade via `exact_mod_cast` + indicator↔card lemma.

- `exists_twin_window_with_two_primes_of_AI_ge_two_from_avg`  
  analytic bridge: if `AI.lower ≥ 2` and heavy set is nonempty (via `avg ≥ τ`),  
  then ∃ `n` with `windowHitCount ≥ 2` for the twin window.

**Design notes:**
- Explicit rewrites for `([0,2]).toFinset` ↔ `{0,2}` (no brittle `simpa/assumption`).
- Casting discipline: prove Nat inequality, `exact_mod_cast` to ℝ, rewrite via the cardinality lemma.
- Imports at top; UTF-8 no BOM; no hidden characters; no global linter disables except a *local* `unnecessarySimpa` in this file.
