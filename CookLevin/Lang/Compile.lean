import CookLevin.Lang.Compile.Core
import CookLevin.Lang.Compile.Encoding
import CookLevin.Lang.Compile.OpMachines
import CookLevin.Lang.Compile.Cmd
import CookLevin.Lang.Compile.OpSound
import CookLevin.Lang.Compile.Assembly
import CookLevin.Lang.Compile.Decider

/-!
# The compiler from programs to Turing machines

`Compile c` is the single-tape Turing machine computing the program `c` of the register
language on the tape encoding `Compile.encodeTape` of its state, together with its
correctness and running-time bounds. This module only imports the parts of the compiler:

- `Compile/Core`       — `CompiledCmd` and generic combinators;
- `Compile/Encoding`   — the tape encoding of states and its inverse;
- `Compile/OpMachines` — the machine for every primitive operation;
- `Compile/RunClear`, `RunMove`, `RunCopyTail`, `RunEqBit` — run lemmas for those machines;
- `Compile/Cmd`        — the compiler itself (`compileCmd`);
- `Compile/OpSound`    — soundness of every primitive operation and of sequencing;
- `Compile/Assembly`   — soundness of branches and loops, `Compile_run_physical_residue`;
- `Compile/Decider`    — the padded decider and computer machines used by `ToMachine`.
-/
