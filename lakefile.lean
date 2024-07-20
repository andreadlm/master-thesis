import Lake
open Lake DSL

package «master_thesis» where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]
  -- add any additional package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "stable"

@[default_target]
lean_lib «MasterThesis» where

@[default_target]
  lean_exe «Compile» where
