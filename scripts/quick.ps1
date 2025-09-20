# scripts/quick.ps1
$null = & { lake build 2>&1 }
powershell -ExecutionPolicy Bypass -File .\scripts\fix-lints.ps1 -DryRun
