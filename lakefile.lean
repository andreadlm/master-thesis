import Lake
open Lake DSL

package «master_thesis» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]

require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "v4.10.0"

-- meta if get_config? doc = some "on" then
require «doc-gen4» from git "https://github.com/leanprover/doc-gen4" @ "v4.10.0"

@[default_target]
lean_lib «MasterThesis» where

lean_exe «l2s» where
