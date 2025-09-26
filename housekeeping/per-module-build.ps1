param(
  [string]$Root   = "Sieve",
  [string]$OutCsv = "build-per-module.csv",
  [string]$OutLog = "build_all.log",
  [string]$Include = "",
  [string]$Exclude = ""
)

$proj = (Get-Location).Path

function Get-ModuleName([string]$file) {
  $full = [IO.Path]::GetFullPath($file)
  $rootFull = [IO.Path]::GetFullPath($proj)
  if (-not $full.StartsWith($rootFull)) { return $null }
  $rel = $full.Substring($rootFull.Length).TrimStart('\','/')
  $rel = $rel -replace '[\\/]', '.'
  $mod = $rel -replace '\.lean$', ''
  return $mod
}

$files = Get-ChildItem -Path $Root -Recurse -Filter *.lean |
  Where-Object { $_.FullName -notmatch '\\\.lake\\' }

$mods = foreach ($f in $files) {
  $m = Get-ModuleName $f.FullName
  if ($m) { $m }
}

if ($Include) { $mods = $mods | Where-Object { $_ -match $Include } }
if ($Exclude) { $mods = $mods | Where-Object { $_ -notmatch $Exclude } }

$results = @()
Remove-Item -Force -ErrorAction SilentlyContinue $OutLog
$start = Get-Date
$i = 0; $n = ($mods | Measure-Object).Count

foreach ($m in $mods) {
  $i++
  Write-Host "[$i/$n] lake build $m"
  $output = & lake build $m 2>&1
  $code = $LASTEXITCODE
  $status = if ($code -eq 0) { "OK" } else { "FAIL" }
  $results += [pscustomobject]@{ Module = $m; Status = $status }
  Add-Content -Path $OutLog -Value "===== $status :: $m ====="
  ($output | Out-String) | Add-Content -Path $OutLog
}

$results | Sort-Object Status, Module | Export-Csv -Path $OutCsv -NoTypeInformation -Encoding UTF8

$ok   = ($results | Where-Object { $_.Status -eq 'OK' } | Measure-Object).Count
$fail = $n - $ok
$elapsed = (Get-Date) - $start
Write-Host "Done. $ok OK, $fail FAIL in $($elapsed.ToString())."
