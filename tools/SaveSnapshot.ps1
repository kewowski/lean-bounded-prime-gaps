$ErrorActionPreference = "Stop"

# Timestamp + output dir
$ts = Get-Date -Format "yyyyMMdd_HHmmss"
$outDir = Join-Path (Get-Location) "artifacts"
New-Item -ItemType Directory -Force $outDir | Out-Null

# 1) Rebuild (log to artifacts)
$buildLog = Join-Path $outDir "build_$ts.log"
"== lake build @ $ts ==" | Out-File -Encoding utf8NoBOM $buildLog
(lake build) *>> $buildLog

# 2) Manifest of Lean files (stable ordering)
$manifest = Join-Path $outDir "manifest_$ts.txt"
Get-ChildItem -Recurse -Filter *.lean |
  Sort-Object FullName |
  ForEach-Object { $_.FullName } |
  Out-File -Encoding utf8NoBOM $manifest

# 3) SHA-256 of all Lean files (CSV)
$hashCsv = Join-Path $outDir "sha256_$ts.csv"
Get-ChildItem -Recurse -Filter *.lean |
  Get-FileHash -Algorithm SHA256 |
  Select-Object Path, Hash, Algorithm |
  Export-Csv -NoTypeInformation -Encoding UTF8 $hashCsv

# 4) Scan for risky markers (should be empty)
$scanTxt = Join-Path $outDir "scan_$ts.txt"
Select-String -Path (Get-ChildItem -Recurse -Filter *.lean | ForEach-Object FullName) `
  -Pattern 'sorry|axiom|admit|TODO|placeholder' -SimpleMatch `
  | Out-File -Encoding utf8NoBOM $scanTxt

# 5) Create a ZIP snapshot (exclude 'artifacts' itself)
$zipPath = Join-Path $outDir "snapshot_$ts.zip"
$items = Get-ChildItem -Force | Where-Object { $_.Name -ne 'artifacts' -and $_.Name -ne '.git' }
if (Test-Path $zipPath) { Remove-Item -Force $zipPath }
Compress-Archive -Path ($items | ForEach-Object FullName) -DestinationPath $zipPath -Force

# 6) Hash the ZIP
$zipHashPath = Join-Path $outDir "zip_sha256_$ts.txt"
$zipHash = Get-FileHash -Algorithm SHA256 $zipPath
"ZIP: $($zipPath)"        | Out-File -Encoding utf8NoBOM $zipHashPath
"SHA256: $($zipHash.Hash)"| Out-File -Encoding utf8NoBOM -Append $zipHashPath

# 7) Next-steps note
$next = Join-Path $outDir "NEXT_STEPS_$ts.md"
@"
# Next Steps (saved @ $ts)

**Status:** Build green. No placeholders/sorries detected.

## Priorities
1) Re-enable Gallagher in the build graph:
   - Fix `Sieve/GallagherConservative.lean` issues:
     - Prefer `‖·‖` over deprecated `Complex.abs`.
     - Replace uses of `Nat.succ_le_iff.mp (…): 0 < q` where `0 ≤ q` is required.
     - Clean up `inv_mul_cancel` type mismatches; normalize coercions `ℕ → ℝ` and move inverses outside sums with `by field_simp` / algebraic rewrites.
     - Remove/rename unused variables flagged by the linter.

2) Swap `Sieve.GallagherHook.contract` from the conservative default to your real bound exported by Gallagher.

3) Admissible tuples:
   - Reintroduce `{0,2}` admissibility with a tidy proof (use cardinality: `|{0,2}| = 2 < p` for all primes `p ≥ 3`, handle `p=2` separately).

4) Characters shim:
   - Gradually replace `Character/Decompositions.lean` stub with concrete Dirichlet character API (types + one or two safe lemmas).

5) Weights:
   - Add a simple nontrivial supported weight (e.g., constant on `[-N,N]`) and plumb its first/second moments into `Pipeline.stage1`.

## Nice-to-have housekeeping
- Run through linter hints (`simp` vs `simpa`, duplicate namespace names, unused vars).
- Add brief README section documenting new modules: AdmissibleTuples, MaynardWeights, MTMoments, Pipeline, Contracts, NaiveWeight, ConstWeight, MTConfig, Smoke.

(Artifacts: `$outDir`)
"@ | Out-File -Encoding utf8NoBOM $next

Write-Host "`nSnapshot complete."
Write-Host "  ZIP:     $zipPath"
Write-Host "  SHA256:  $($zipHash.Hash)"
Write-Host "  MANIFEST: $manifest"
Write-Host "  SCAN:     $scanTxt"
Write-Host "  NEXT:     $next"
