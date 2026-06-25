import Complexity.Lang.Compile.Core
import Complexity.Lang.Compile.Encoding
import Complexity.Lang.Compile.OpMachines
import Complexity.Lang.Compile.Cmd
import Complexity.Lang.Compile.RunLemmas
import Complexity.Lang.Compile.OpSound
import Complexity.Lang.Compile.Assembly
import Complexity.Lang.Compile.Decider

/-! # The Cmd → FlatTM compiler (Part 3.3 / 3.4 of ROADMAP) — facade

`Compile` emits a `FlatTM` for each `Cmd`. The compiler is the one-time
engineering investment that justifies the layer's existence: every downstream
verifier and reduction is written as a `Cmd`, and the compiler produces a real
polynomial-time Turing machine.

This file is now a thin **facade**: it imports the compiler's submodule DAG so
that `import Complexity.Lang.Compile` (as `PolyTime.lean` does) pulls in the
whole compiler. The split (see `REFACTOR-HANDOFF.md`) replaced a single
26K-line module so the build parallelises and edits rebuild only the touched
module:

- `Compile/Core`       — `CompiledCmd`, `joinTwoHalts`, `rewindBracket`, combinators.
- `Compile/Encoding`   — `encodeTape`/`decodeTape` + `BitState`/`ValidResidue`.
- `Compile/OpMachines` — the per-`Op` TM machine *defs* + shape lemmas.
- `Compile/Cmd`        — `compileOp`/`compileSeq`/`compileIfBit`/`compileTestBit`/
                         the `forBnd` machines + `compileCmd`/`Compile`/`exit`.
- `Compile/RunLemmas`  — every per-op *run/behaviour* lemma + the residue toolkit.
- `Compile/OpSound`    — `compileOp_sound_physical_residue` + `compileSeq` soundness.
- `Compile/Assembly`   — the C6 tester, the C2 assembly toolkit, `compileIfBit`/
                         `compileForBnd` soundness + the `forBnd` loop run stack,
                         `run_physical_residue_gen`/`Compile_run_physical_residue`,
                         and `bitDeciderTM`/`bitDecider_run`.
- `Compile/Decider`    — the WALL: `padRegsTM`/`paddedBitDecider`/`paddedCompute`.

Fixed commitments: `CompiledCmd` carries an exit state; the alphabet is
`sig = 4` (delimiter `0`, shifted bits `1`/`2`, terminator `3 = endMark`),
so inputs are bit-strings (`Compile.BitState`); the physical contract is
**residue-tolerant** (`encodeTape output ++ ValidResidue residue`). -/
