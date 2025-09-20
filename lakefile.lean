import Lake
open Lake DSL

package test_lean_modules where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.22.0-rc4"

@[default_target]
lean_lib TestLeanModules where
  roots := #[`Sieve, `MaynardTao, `Character]
