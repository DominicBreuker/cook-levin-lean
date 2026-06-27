import Complexity.Lang.Compile.RunClear
import Complexity.Lang.Compile.RunMove
import Complexity.Lang.Compile.RunCopyTail
import Complexity.Lang.Compile.RunEqBit

/-! # `Compile/RunLemmas` — per-op run/behaviour lemmas + residue toolkit (facade)

This file is now a thin **facade**: the per-op run/behaviour layer was split
into a four-module DAG (refactor Phase 1-refinement, see `REFACTOR-HANDOFF.md`)
so that an edit to one gadget's run stack no longer recompiles the others.
Kept as the single public entry point for the run layer (the top-level
`Compile.lean` facade imports it). The internal consumers (`OpSound`, `Assembly`,
`Decider`) import the four Run modules **directly** instead, so this facade is
**off their build critical path**: a no-content facade is a pure ~2.3s import
gate, and bypassing it shortens the serial `RunEqBit → OpSound → … → Decider`
chain.

The DAG, in dependency order:

- `Compile/RunClear`    — the two append ops' per-op soundness,
                          `compileSeq_compose_physical`, the shared
                          `ValidResidue`/`TapeOK` residue toolkit, and the
                          `clear` run stack (`clearRegionTM_run`).
- `Compile/RunMove`     — the move-one-bit / dual-target transfer gadgets,
                          residue-tolerant `navigateAndTest` reading
                          (`skipped_*`), and the `compileTestBit` run lemmas.
- `Compile/RunCopyTail` — the cursor-copy (`copy`) and `tail` run stacks.
- `Compile/RunEqBit`    — the `eqBit` no-grow consume-loop run stack
                          (ending at `opEqBitNG_run`). -/
