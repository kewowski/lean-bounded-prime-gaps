param([switch]$VerboseChecks)

$ErrorActionPreference = "Stop"
Write-Host "=== Stage-3 / Analytic smoke build ==="

# Core modules to keep green
$targets = @(
  "Sieve.Stage3Exports",
  "Sieve.Stage3TwinGap",
  "Sieve.Stage3PrimesEndToEnd",
  "Sieve.Analytic.BVMainStatement",
  "Sieve.Analytic.BVMainStatementWrapper",
  "Sieve.Analytic.RunTwinWindowFromBVMain",
  "Sieve.EndToEndTwinWindowDemo",
  "Sieve.Tests.Stage3TwinWindowSmoke"
)

Write-Host "Building: $($targets -join ', ')"
& lake build @targets
if ($LASTEXITCODE -ne 0) { throw "lake build failed." }

if ($VerboseChecks) {
  Write-Host "`n=== Extra checks ==="
  # avgOver visibility probe
  $hits = Select-String -Path 'Sieve\**\*.lean' -Pattern '\bavgOver\b' -CaseSensitive -ErrorAction SilentlyContinue
  Write-Host ("avgOver occurrences: " + ($hits | Measure-Object).Count)

  # Ensure no accidental sorrys
  $sorries = Select-String -Path 'Sieve\**\*.lean' -Pattern '\bsorry\b' -CaseSensitive -ErrorAction SilentlyContinue
  if ($sorries) {
    Write-Warning "Found 'sorry' in:"
    $sorries | Format-Table Path, LineNumber, Line -AutoSize
  } else {
    Write-Host "No 'sorry' found under Sieve/."
  }
}

Write-Host "`nAll good ✅"
