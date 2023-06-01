import Lake
open Lake DSL

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"

package «sparky» {
  -- add package configuration options here
}

@[default_target]
lean_lib «Sparky» {
  -- add library configuration options here
}