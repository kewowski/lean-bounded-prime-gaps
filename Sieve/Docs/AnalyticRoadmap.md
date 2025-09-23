# Analytic Roadmap (BV/EH Lower Bound Sketch)

Goal: Provide a formal, Stage-3-consumable analytic lower bound
`lower ≤ avgOver (heavySet W τ) (windowSum H (hitIndicator HS))`
without implementing the hard analysis yet. Keep the repo green and leaf-like.

---

## Where to define constants

File: Sieve/Analytic/Constants.lean  
Type: Sieve.Analytic.BVParams

Fields:
- θ : ℝ — distribution exponent (BV ≈ 1/2, EH up to 1).
- k : ℕ — Maynard weight dimension.
- Cmain : ℝ — main-term constant for the symbolic lower bound.
- Cerr  : ℝ — error-term constant (with Cerr_nonneg : 0 ≤ Cerr).
- x0    : ℝ — “sufficiently large” threshold (with x0_nonneg : 0 ≤ x0).

These are inputs chosen by the caller/demo. Ranges are documented but not enforced here.

---

## Where to state the eventual analytic lemmas

File: Sieve/Analytic/LargeSieveCore.lean  
Type: Sieve.Analytic.BVToolbox

Fields (placeholders, Prop for now — matches current code):
- large_sieve_bound
- dirichlet_orthogonality_sum
- partial_summation_real

Later milestones can refine/extend these to precise inequalities with constants.

---

## How `bvSketch` reduces `le_avg` to a single proof argument

File: Sieve/Analytic/BVSketch.lean

Current symbolic lower formula (keeps repo green):
- def lowerFormula (P : Type) … : ℝ := 0
  (The formula deliberately does nothing yet; it wires the interface while postponing analysis.)

Provider constructor (matches code):
- def bvSketch (P : Type) (TB : BVToolbox)
    (proof : ∀ W τ H HS hne,
      lowerFormula P W τ H HS hne ≤
      Sieve.Stage3.avgOver (Sieve.MTCore.heavySet W τ)
        (Sieve.Stage3.windowSum H (Sieve.Stage3.hitIndicator HS)))
    : AvgWindowHitLB

All hard analysis is deferred to the `proof` argument, keeping the repo green and enabling Stage-3 use today.

Planned refinement (next milestone):
- Switch to P := BVParams and set a realistic lowerFormula (main − error depending on θ, k, τ, |supp W|, logs),
  then prove/assume the corresponding proof.

---

## How Stage-3 wrappers consume the bound (≥1 / ≥2)

File: Sieve/RunBVSketchTwinDemo.lean

- Instantiate AI := bvSketch P TB proof.
- If you show 1 ≤ AI.lower …, pass to the Stage-3 wrapper to get “∃ a prime in the window”.
- If you show 2 ≤ AI.lower … on {0,2}, pass to the twin wrapper to get a twin prime pair.

The demo keeps actual wrapper lemmas abstract (arguments) so the file stays leaf-like and fast.

---

## Import & dependency hygiene

- New analytic files are leaf modules; do not import big “exports” hubs to avoid cycles.
- Demos may import hubs (e.g. prime façade); core analytic modules import only what they need.

---

## Next steps (after Milestone 1)

1. Replace lowerFormula with an explicit expression depending on (θ, k, τ, |supp W|, log-factors).
2. Refine BVToolbox fields from Prop to concrete inequalities with constants; add fields as needed.
3. Introduce BVMainTheorem (parameterized by BVParams and toolbox facts) and set proof := BVMainTheorem.
4. Implement toolbox lemmas (partial summation, dispersion/large sieve) in small, separate files to keep builds fast.
## From a numeric bound to Stage-3 conclusions

Given P : BVParams and a proof hAI : BVMainStatement P TB, set AI := AI_of_BV P TB hAI.
If you know a numeric threshold on the parametric lower bound, you can plug it into the wrappers:

`lean
-- Build the provider from your main statement proof:
let AI := Sieve.Analytic.AI_of_BV P TB hAI

-- Suppose you established a numeric bound like: 1 ≤ P.Cmain - P.Cerr
-- (e.g., from your constants ledger and error tracking)
-- Then you can lift it to the required hypothesis for any window H:
have h1 :
  (1 : ℝ) ≤ AI.lower W τ H (Sieve.Stage3.primeHS cfg) hne := by
  -- supply your arithmetic here; e.g.
  -- exact (show 1 ≤ P.Cmain - P.Cerr from h_num_ge_one)
  admit  -- replace with your inequality proof

-- ≥ 1 ⇒ some prime in the window H
have ⟨n, hnA, h, hhH, hp⟩ :=
  Sieve.Stage3.exists_prime_in_window_of_AI_ge_one_from_avg
    (AI := AI) (W := W) (τ := τ) (H := H) (cfg := cfg)
    (hpos := hpos) (hτleavg := hτleavg) (h1 := h1)

-- If you instead have a stronger numeric bound on the twin window {0,2}:
have h2 :
  (2 : ℝ) ≤ AI.lower W τ (([0, 2] : List ℤ).toFinset) (Sieve.Stage3.primeHS cfg) hne := by
  -- exact (show 2 ≤ P.Cmain - P.Cerr from h_num_ge_two)
  admit  -- replace with your inequality proof

-- ≥ 2 on the twin window ⇒ a twin prime pair
have ⟨p, hp0, hp2⟩ :=
  Sieve.Stage3TwinGap.exists_twin_primes_of_AI_ge_two_from_avg
    (AI := AI) (W := W) (τ := τ) (cfg := cfg)
    (hpos := hpos) (hτleavg := hτleavg) (h2 := h2)
Tips

To turn a comparison like P.Cerr ≤ P.Cmain - 1 into 1 ≤ P.Cmain - P.Cerr, use simple algebra
(e.g. linarith) or start from BVParams.main_minus_error_nonneg_of_le and rewrite.

Use Sieve.Stage3.heavySet_nonempty_of_tau_le_avg to obtain hne : (heavySet W τ).Nonempty from
τ ≤ average. This keeps the Stage-3 wrappers ready to consume your bound.
