# Sieve pipeline (Maynard–Tao scaffold)

## Quick build

## Demo
The demo builds Stage 1 using a constant weight over a symmetric window:
- Config: `Sieve.Examples.trivialPipeline`
- Weight:  `Sieve.ConstWeight.const`
- Runner:  `Sieve.Run`

## Modules
- `Character/Decompositions.lean` — minimal character API shim
- `Sieve/AdmissibleTuples.lean`  — admissibility predicate & translate
- `Sieve/MaynardWeights.lean`    — weight interfaces
- `Sieve/LinearSieveBounds.lean` — GallagherBound & SieveContract
- `Sieve/Contracts.lean`         — conservative contract
- `Sieve/MTMoments.lean`         — first/second moments + lemmas
- `Sieve/Pipeline.lean`          — Config + stage1 glue
- `Sieve/NaiveWeight.lean`       — zero weight
- `Sieve/ConstWeight.lean`       — constant weight builder
- `Sieve/GallagherConservative.lean` — exported conservative bound
- `Sieve/GallagherHook.lean`     — contract wired to Gallagher bound
- `Sieve/Smoke.lean`             — smoke tests
- `Sieve/Run.lean`               — simple runnable demo
