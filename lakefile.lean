import Lake
open Lake DSL

package «cook-levin-lean» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib CookLevin where
  srcDir := "CookLevin"
  roots := #[`Basic, `Complexity.NP.SAT.CookLevin]

lean_exe «cook-levin-lean» where
  root := `Main
