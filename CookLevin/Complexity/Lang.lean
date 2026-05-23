import Complexity.Lang.Syntax
import Complexity.Lang.Semantics
import Complexity.Lang.ShiftTape
import Complexity.Lang.Navigate
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
- `Lang.Navigate`   : `scan_to_delim`, the register-navigation atom
                      (find a register's terminating delimiter) every
                      `Op` uses to locate register `dst` (Risk C1).
- `Lang.Compile`    : `Compile : Cmd → FlatTM`, soundness theorem.
- `Lang.PolyTime`   : `inTimePolyLang`, `PolyTimeComputableLang`, bridges
                      to `inTimePoly`, `polyTimeComputable`, and `inNP`.

See `ROADMAP.md` (Part 3) for the strategic rationale. -/
