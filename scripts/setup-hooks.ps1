# scripts/setup-hooks.ps1
# Installs a pre-commit hook that runs scripts/ci.ps1 and blocks commits on failure.

$hookDir = ".git/hooks"
if (-not (Test-Path $hookDir)) {
  Write-Host "No .git folder found. Run this from the repo root after 'git init' or cloning." -ForegroundColor Yellow
  exit 1
}

# Bash-style hook (works with Git Bash). ASCII => no BOM.
$bashHook = @"
#!/usr/bin/env bash
# Pre-commit CI gate
pwsh -ExecutionPolicy Bypass -File scripts/ci.ps1 -VerboseOutput
code=\$?
if [ \$code -ne 0 ]; then
  echo "[pre-commit] CI gate failed (exit \$code)" 1>&2
  exit \$code
fi
exit 0
"@
Set-Content -Path "$hookDir/pre-commit" -Value $bashHook -Encoding Ascii

# PowerShell hook (for environments that execute .ps1 hooks)
$psHook = @"
# Pre-commit CI gate (PowerShell)
powershell -ExecutionPolicy Bypass -File scripts/ci.ps1 -VerboseOutput
if (\$LASTEXITCODE -ne 0) { exit \$LASTEXITCODE }
exit 0
"@
Set-Content -Path "$hookDir/pre-commit.ps1" -Value $psHook -Encoding UTF8

Write-Host "Installed pre-commit hooks." -ForegroundColor Green
