import Complexity.Lang.Syntax
import Complexity.Lang.Semantics
import Complexity.Lang.ShiftTape
import Complexity.Lang.Navigate
import Complexity.Lang.AppendGadget
import Complexity.Lang.Compile
import Complexity.Lang.PolyTime

set_option autoImplicit false

/-! # The Lang layer — aggregator

A single import that brings in the entire layer skeleton:

- `Lang.Syntax`     : `Op`, `Cmd`, `State`, output convention.
- `Lang.Semantics`  : `Cmd.eval`, `Cmd.cost` (axiomatic), algebraic laws.
- `Lang.ShiftTape`  : `insertCarryTM` + `insertCarryTM_run`, the shared
                      single-tape "insert one symbol" gadget every
                      length-*increasing* `Op` builds on (Risk C1).
- `Lang.Navigate`   : `scan_to_delim` / `scan_to_end`, the register-
                      navigation atoms (find a register's terminating
                      delimiter / the end-of-tape terminator) plus their
                      trajectory lemmas (`scan_to_mark_traj`) used to glue
                      a scan ahead of a follow-on machine (Risk C1).
- `Lang.AppendGadget`: `scan_then_insert_run`, the scan-to-delimiter ⨾
                      insert composition realizing `appendOne`/`appendZero`
                      on register 0 — the first `composeFlatTM_run`
                      exercise in the layer (Risk C1).
- `Lang.Compile`    : `Compile : Cmd → FlatTM`, soundness theorem.
- `Lang.PolyTime`   : `inTimePolyLang`, `PolyTimeComputableLang`, bridges
                      to `inTimePoly`, `polyTimeComputable`, and `inNP`.

See `ROADMAP.md` (Part 3) for the strategic rationale. -/
