# Analytic Bridge — Single-Gateway Spec (BV/EH → Stage-3)

This document explains how **any** Bombieri–Vinogradov / Elliott–Halberstam style estimate plugs into Stage-3 via a single inequality—no Stage-2/3 refactors.

---

## The Gateway (what you must prove)

For your chosen BV parameter pack `P : BVParams`, provide:

    def BVMainIneq (P : BVParams) : Prop :=
      ∀ (W : Sieve.MaynardWeights.Weight) (τ : ℝ)
        (H : Finset ℤ) (HS : Sieve.Stage3.HitSystem)
        (_hne : (Sieve.MTCore.heavySet W τ).Nonempty),
        P.lowerFormula
          ≤ Sieve.Stage3.avgOver (Sieve.MTCore.heavySet W τ)
              (Sieve.Stage3.windowSum H (Sieve.Stage3.hitIndicator HS))

Intuition: your analysis supplies a **uniform lower bound** `P.lowerFormula` for the heavy-set average of window hits, across all weights, windows, and hit systems.

---

## Turning the inequality into the Stage-3 interface

Given `h : BVMainIneq P`, build the interface used by Stage-3:

    import Sieve.Analytic.BVMainIneq
    def AI : AvgWindowHitLB := Sieve.Analytic.AI_of_BV_ofIneq P h

Under the hood this packages your constant lower bound `P.lowerFormula` with the proof `h` via the tiny constructor stack:

- AnalyticInputs.mk (existing)
- AnalyticInputs.ofLower (thin wrapper)
- AI_of_BV_fromLowerBound / AI_of_BV_ofIneq (realization)

This keeps Stage-2/3 **unchanged**.

---

## Using the bridge (examples in repo)

- **Type-plumbing wire (always green):**  
  `Sieve/Analytic/BVMainStatementWire.lean` defines `AI_of_BV` using `lower := avg` (tautological, no analysis needed). This is a safe default.

- **Realized bridge:**  
  `Sieve/Analytic/BVMainRealize.lean` and `Sieve/Analytic/BVMainIneq.lean` show how to feed a real inequality and obtain `AvgWindowHitLB`.

- **Smoke demos:**  
  - `Sieve/Analytic/RunBVBridgeSmoke.lean` — uses the wire AI + Stage-3 lemma.  
  - `Sieve/Analytic/RunBVMainIneqDemo.lean` — uses the **realized** AI from `BVMainIneq`.

---

## Stage-3 consumption (already in place)

Once you have `AI : AvgWindowHitLB`, Stage-3 bridge lemmas apply directly, e.g.

    open Sieve
    theorem exists_heavy_hit_of_lb_ge_one
      (AI : AvgWindowHitLB) (W : MaynardWeights.Weight) (τ : ℝ)
      (H : Finset ℤ) (HS : Stage3.HitSystem)
      (hne : (MTCore.heavySet W τ).Nonempty)
      (h1 : 1 ≤ AI.lower W τ H HS hne) :
      ∃ n ∈ MTCore.heavySet W τ, ∃ h ∈ H, HS.isHit (n + h)

From here, the Stage-3 façade extracts primes/twins/etc. per the existing demos.

---

## What to prove next (outside this typed bridge)

You can discharge `BVMainIneq P` by chaining:

1. Discrete partial summation (your per-modulus sums)  
2. Large sieve over progressions (constant-carrying)  
3. Orthogonality identity (already implemented: `OrthogonalityIdentityImpl`)  
4. Trivial nonnegativity/triangle inequalities (fast, already present)

Keep each step **tiny**, algebraic, and leaf-imported.

---

## File Map (for quick reference)

- Sieve/Analytic/BVMainIneq.lean — gateway `BVMainIneq` and `AI_of_BV_ofIneq`
- Sieve/Analytic/BVMainRealize.lean — generic “from lower bound” constructor
- Sieve/Analytic/AIConstructors.lean — thin wrapper `AnalyticInputs.ofLower`
- Sieve/Analytic/BVMainStatementWire.lean — always-green wire (lower := avg)
- Sieve/Analytic/RunBVBridgeSmoke.lean — smoke using the wire AI
- Sieve/Analytic/RunBVMainIneqDemo.lean — smoke using the **realized** AI
- Sieve/Analytic/OrthogonalityIdentityImpl.lean — orthogonality helper
- Sieve/Analytic/BVMainHelpers.lean, BVAlgebraLemmas.lean, ConstantsMakers.lean — small algebra helpers

---

### UI/Copy Hygiene (for PowerShell heredocs in chat)

- When sending a PowerShell here-string in chat, **do not use triple backticks inside the here-string content**.  
  Use 4-space-indented code blocks or escape backticks. Otherwise the chat UI renders multiple “Copy” blocks.
