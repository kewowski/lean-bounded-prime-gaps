param()
$ErrorActionPreference = "Stop"

# Ensure we run at repo root
$repo = (git rev-parse --show-toplevel).Trim()
Set-Location $repo

Write-Host "[pre-commit] Lints (dry run)..." -ForegroundColor Cyan
powershell -NoProfile -ExecutionPolicy Bypass -File "$repo/scripts/fix-lints.ps1" -DryRun

Write-Host "[pre-commit] Building..." -ForegroundColor Cyan
& lake build
if ($LASTEXITCODE -ne 0) {
  Write-Error "lake build failed"
  exit $LASTEXITCODE
}

Write-Host "[ci] OK: build + lints clean"
exit 0