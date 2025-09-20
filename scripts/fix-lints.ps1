param(
  [switch]$DryRun  # show what would change, don’t write files
)

function ReplaceSimpaWithSimp([string]$file,[int]$line){
  $lines = Get-Content $file
  $i = $line - 1
  if ($i -lt 0 -or $i -ge $lines.Count) { return }
  $orig = $lines[$i]
  # Only flip when the line doesn’t use `using`
  if ($orig -match '\bsimpa\b' -and $orig -notmatch '\busing\b') {
    $new = [regex]::Replace($orig,'\bsimpa\b','simp')
    if ($new -ne $orig) {
      if ($DryRun) {
        Write-Host ("DRY: simpa->simp  {0}:{1}`n    {2}`n    {3}" -f $file,$line,$orig,$new)
      } else {
        $lines[$i] = $new
        Set-Content -Path $file -Value $lines -Encoding utf8NoBOM
        Write-Host ("fix: simpa->simp  {0}:{1}" -f $file,$line)
      }
    }
  }
}

function RemoveSimpArg([string]$file,[int]$line,[string]$arg){
  $lines = Get-Content $file
  $i = $line - 1
  if ($i -lt 0 -or $i -ge $lines.Count) { return }
  $orig = $lines[$i]
  if ($orig -notmatch '\bsimp\b') { return }
  $argEsc = [regex]::Escape(($arg.Trim()))
  $new = $orig
  # remove ", arg" and "arg, " inside the simp brackets on this line
  $new = [regex]::Replace($new, "\s*,\s*$argEsc\b", "")
  $new = [regex]::Replace($new, "\b$argEsc\s*,\s*", "")
  # if brackets end up as just that arg, drop it to []
  $new = $new -replace "\[\s*$argEsc\s*\]", "[]"
  if ($new -ne $orig) {
    if ($DryRun) {
      Write-Host ("DRY: drop simp arg '{0}'  {1}:{2}`n    {3}`n    {4}" -f $arg,$file,$line,$orig,$new)
    } else {
      $lines[$i] = $new
      Set-Content -Path $file -Value $lines -Encoding utf8NoBOM
      Write-Host ("fix: drop simp arg '{0}'  {1}:{2}" -f $arg,$file,$line)
    }
  }
}

# Run a build and capture output (stderr -> stdout)
$out = & { lake build 2>&1 }
$out | Tee-Object -FilePath .\scripts\_last_build_output.txt | Out-Null

# Parse warnings and apply fixes
for ($i=0; $i -lt $out.Count; $i++) {
  $line = $out[$i]

  # try 'simp' instead of 'simpa'
  if ($line -match '^warning:\s+(.+?):(\d+):\d+:\s+try ''simp'' instead of ''simpa''') {
    $file = $matches[1]; $ln = [int]$matches[2]
    if ($file -like '*.lean' -and (Test-Path $file)) {
      ReplaceSimpaWithSimp $file $ln
    }
    continue
  }

  # This simp argument is unused:
  if ($line -match '^warning:\s+(.+?):(\d+):\d+:\s+This simp argument is unused:') {
    $file = $matches[1]; $ln = [int]$matches[2]
    # the next non-empty line holds the arg name
    $j = $i + 1
    while ($j -lt $out.Count -and [string]::IsNullOrWhiteSpace($out[$j])) { $j++ }
    if ($j -lt $out.Count) {
      $arg = $out[$j].Trim()
      if ($file -like '*.lean' -and (Test-Path $file) -and $arg) {
        RemoveSimpArg $file $ln $arg
      }
      $i = $j
    }
    continue
  }
}
