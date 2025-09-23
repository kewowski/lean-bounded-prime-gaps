## Simp & Rewrite Style (lint-first)

**Goal:** avoid error loops and keep builds green by writing proofs that simplify cleanly and predictably.

### Rewrites vs. simplification
- Use `rw` for **structural** equalities first (e.g. `Finset.sum_insert`, `Finset.sum_comm`, `Finset.sum_filter`), then finish with a plain `simp`.
- Avoid `rw IH` unless the goal is **structurally identical** to IH’s LHS/RHS. Prefer chaining equalities with `.trans` or a small `calc`.
- Don’t globalize `eq_comm` or similar; flip sides **locally** only where needed.

### `simp` discipline
- If the goal matches after simplification, **use `simp`**, not `simpa`.
- Keep `simp` argument lists **minimal**. If the linter says “unused simp arg,” remove it.
- Prefer `have h := …; simp [lemmas] at h; exact h` to avoid brittle `simpa … using …`.

### Finite sums patterns
- Swap sums with `Finset.sum_comm`.
- Pointwise rewrites inside sums with `Finset.sum_congr rfl (by intro x hx; …)`.
- For indicator spikes like `∑ x∈s, (if x = t then c else 0)`, use **`Finset.sum_filter`** and then reason about the filtered set (`∅` / `{t}`), rather than `sum_insert` gymnastics.

### Residues & orthogonality
- Canonical guard is `if n % q = r then … else …`. Convert to `r = n % q` **pointwise** with a `by_cases h : r = n % q; simp [h]`.
- Membership fact you will need:  
  `have hmem : n % q ∈ Finset.range q := Finset.mem_range.mpr (Nat.mod_lt n hq)` (requires `hq : 0 < q`).

### Branching & classical
- Localize `classical` inside proofs; don’t open it for whole files.
- In `by_cases`, name only what you’ll actually use (e.g. `have ht_not : t ∉ s := …`) and let `simp` consume it—don’t pass unused facts to `simp`.

### Perf & lints workflow
- After **every** file edit: `lake build Module.Name; lake build`.
- Fix **all warnings immediately** (unused simp args, “try `simp` instead of `simpa`”) before proceeding.
- Keep compile-touch lemmas trivial (`… : True := True.intro`)—no `simp` or `simpa` inside them.
