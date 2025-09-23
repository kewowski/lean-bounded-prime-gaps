# Adding Your Analytic Lower Bound (BV/EH Template)

Goal: Provide a numeric lower bound for avgOver (heavySet W τ) (windowSum H (hitIndicator HS))
via the interface Sieve.Analytic.AvgWindowHitLB.

Where to start:
See: Sieve/AnalyticBVTemplate.lean

Example:
  def bvTemplateAsLower : AvgWindowHitLB := avgAsLower

Replace bvTemplateAsLower with your real bound:
- Keep the same structure (.lower and .le_avg).
- Set .lower to your numeric expression (e.g. from BV/EH).
- Prove .le_avg : lower ≤ avgOver(heavySet τ) (windowSum H (hitIndicator HS)).

How it plugs into Stage 3:
Use the existing wrappers (no refactors needed):
- exists_prime_in_window_of_AI_ge_one_from_avg
- exists_atLeast_k_primes_in_window_of_AI_ge_k_from_avg
- Twin specializations:
  - exists_prime_in_twin_window_of_AI_ge_one_from_avg
  - Stage3TwinGap.exists_twin_primes_of_AI_ge_two_from_avg (≥ 2 ⇒ twin prime pair)

Typical usage sketch:
  -- Provide your AI
  def AI := Sieve.Analytic.bvTemplateAsLower  -- replace with your real bound

  -- Hypotheses (heavy-set derived from τ ≤ average)
  have hpos   : 0 < W.support.card := ...
  have hτleavg : τ ≤ (∑ m ∈ W.support, W.w m) / (W.support.card : ℝ) := ...

  -- Analytic inequalities, proven in your module:
  have h1 : (1 : ℝ) ≤ AI.lower W τ H (Sieve.Stage3.primeHS cfg)
    (Sieve.Stage3.heavySet_nonempty_of_avg_ge (W := W) (τ := τ) hpos hτleavg) := ...
  have h2 : (2 : ℝ) ≤ AI.lower W τ (([0, 2] : List ℤ).toFinset) (Sieve.Stage3.primeHS cfg)
    (Sieve.Stage3.heavySet_nonempty_of_avg_ge (W := W) (τ := τ) hpos hτleavg) := ...

  -- Extract witnesses:
  have ⟨n, hnA, h, hhH, hp⟩ :=
    Sieve.Stage3.exists_prime_in_twin_window_of_AI_ge_one_from_avg
      (AI := AI) (W := W) (τ := τ) (cfg := cfg)
      (hpos := hpos) (hτleavg := hτleavg) (h1 := h1)

  have ⟨p, hp0, hp2⟩ :=
    Sieve.Stage3TwinGap.exists_twin_primes_of_AI_ge_two_from_avg
      (AI := AI) (W := W) (τ := τ) (cfg := cfg)
      (hpos := hpos) (hτleavg := hτleavg) (h2 := h2)

House rules checklist:
- Keep modules green (no sorry, no brittle rewrites).
- Use robust simp/calc patterns.
- Avoid heavy norm_num/#find in core proofs.
- Prefer subset/monotonicity lemmas and clean Finset.sum_* patterns.

See also:
- Sieve/Stage3TwinGap.lean (≥ 2 ⇒ twin primes extraction)
- Sieve/RunAnalyticBVTemplateDemo.lean (type-check demo)
- Sieve/RunStage3TwinGapTwinPrimesDemo.lean (twin demo)
