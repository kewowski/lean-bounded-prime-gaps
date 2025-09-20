# scripts/ci.ps1
# Fails if:
#  - build errors
#  - common lint smells show up ("try 'simp'", "unused simp arg", invalid import)
#  - the linter fixer would make changes (detected via -DryRun)
param(
  [switch]$VerboseOutput
)

# 1) Full build (capture stderr)
$build = & { lake build 2>&1 }
$code  = $LASTEXITCODE
$build | Tee-Object -FilePath .\scripts\_ci_build_output.txt | Out-Null

# 2) Patterns to watch (tuned to your recent issues)
$warnPatterns = @(
  "try 'simp' instead of 'simpa'",
  "This simp argument is unused:",
  "invalid 'import' command, it must be used in the beginning of the file"
)

$found = @()
foreach ($p in $warnPatterns) {
  $hits = $build | Select-String -Pattern $p
  if ($hits) { $found += $hits }
}

# 3) Would the fixer change anything?
$dry = & { powershell -ExecutionPolicy Bypass -File .\scripts\fix-lints.ps1 -DryRun 2>&1 }
$needsFix = $dry | Select-String -Pattern '^DRY:' 

# 4) Report & exit
if ($VerboseOutput) {
  if ($found) { "`n[ci] lint smells detected:`n" + ($found | ForEach-Object { " - " + $_.Line }) | Write-Host }
  if ($needsFix) { "`n[ci] linter fixer would change files:" | Write-Host; $needsFix | ForEach-Object { " - " + $_ } | Write-Host }
}

if ($code -ne 0) {
  Write-Host "`n[ci] build failed (exit $code)" -ForegroundColor Red
  exit $code
}
if ($found.Count -gt 0 -or $needsFix) {
  Write-Host "`n[ci] failing due to lint smells" -ForegroundColor Red
  exit 1
}

Write-Host "`n[ci] OK: build + lints clean" -ForegroundColor Green
exit 0
