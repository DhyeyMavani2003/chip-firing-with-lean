import Lake
open Lake DSL

package "chip-firing-with-lean" where
  version := v!"0.1.0"
  keywords := #["math"]
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]
  moreLinkArgs := #[
    "-L./.lake/packages/LeanCopilot/.lake/build/lib",
    "-lctranslate2"
  ]

require "leanprover-community" / "mathlib" @ "v4.29.0"
require Paperproof from git "https://github.com/Paper-Proof/paperproof.git"@"main"/"lean"

@[default_target]
lean_lib «ChipFiringWithLean» where
  -- add any library configuration options here
