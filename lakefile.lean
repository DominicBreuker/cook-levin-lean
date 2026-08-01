import Lake
open Lake DSL

package «cook-levin-lean» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

-- `Complexity` is the ONLY root, deliberately: it transitively imports every
-- module, which is what makes the whole-library axiom sweep at the bottom of
-- `Complexity.lean` cover the whole library. A second root would be a module
-- the gate does not check — do not add one without extending the sweep.
@[default_target]
lean_lib CookLevin where
  srcDir := "CookLevin"
  roots := #[`Complexity]
