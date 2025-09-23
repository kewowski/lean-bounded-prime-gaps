# Project House Rules (concise)

## Build & Run
- Standard command for edits: **never** call `lean --make` in scripts.
  Use exactly:
  
      lake build Module.Name; lake build
  
  (This keeps output clean and matches our CI expectations.)

- Exactly **one PowerShell command per turn** when collaborating here.

## File Edits
- For **Lean files**, always write the **entire file** using a single heredoc and then build:
  
      @'
      -- full file content
      '@ | Set-Content path\to\File.lean -Encoding utf8NoBOM; lake build Module.Name; lake build

- Keep analytic modules as **leaf modules** (no hub imports). Demos may import hubs.

## Linting & Tactics
- Fix linters immediately.
  - Prefer `simp` when the goal matches.
  - Replace deprecated sums: use `∑ x ∈ s, f x`.
  - Remove unused simp args and variables.
- Keep proofs tiny: `simp`, `rw`, short `calc`. Avoid heavy tactics.

## UI/Copy Hygiene (Chat → PowerShell here-strings)
- Inside PowerShell here-strings posted in chat, **do not use triple backticks**.
  - Use 4-space indented code or escape backticks.
  - This avoids multiple “Copy” blocks and copy-paste breakage.
