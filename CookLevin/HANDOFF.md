# Handoff: S3 migration — `⪯p'` infrastructure landed (Task 4 partial)

This continues the **S3 migration** (route the framework's `red_inNP`/`⪯p`
through the computable "Lang" layer). **Task 3 — the framework decider bridge
`inNPLang → inNP`** — is **assembled** (`inNPLang_to_inNP`), sorry-free modulo
one focused obligation (`Compile_run_physical`, Risk C2). The earlier step
**C5a `map_fst`** is closed, `sorry`-free, and axiom-clean.

**This pass (Task 4 — `⪯p` migration prep)** lands the additive infrastructure
for the next step: `polyTimeComputable'_id` and `polyTimeComputable'_comp_lang`
(framework-level helpers built on the canonical layer), the new
**`ReductionWitness'`/`⪯p'`** additive types with reflexivity, transitivity,
and the bridges `⪯p' → ⪯p` and `PolyTimeComputableLang' f → P ⪯p' Q`. Also
landed: extra `LangEncodable` instances (`Bool`, `Unit`, `List Bool`), the
**generic `LangEncodable (List α)`** (length-prefixed encoding, lower priority
than the `List Nat = id` shortcut), and `Compile_polyBound` closed from
`Compile_sound`. The generic list instance is **the migration unlock**: it
makes chain types like `cnf = List (List (Bool × Nat))` and
`cnf × assgn` *derive their canonical encoding automatically* — the inputs
the canonical `DecidesLang'`/`PolyTimeComputableLang'` need.

Read for direction first: `README.md`, `CookLevin/ROADMAP.md` (*The plan from
here*, step 2, and the Risk register rows **C5a/C10/C6/C2**).

---

## Update: Task 3 (the decider bridge) is now done — what landed

In `CookLevin/Complexity/Lang/Compile.lean`:

- **C6 bit-test gadget `Compile.bitTestTM`** — a 3-state, single-tape, sig-4
  `FlatTM` that reads tape register `0`'s first symbol (`2` = shifted `1` =
  accept, `1` = shifted `0` = reject) and halts in a *distinct* state (`1`/`2`).
  Validity + run lemmas (`bitTestTM_run_two`/`_one`) are **`sorry`-free**
  (encoding-only, independent of `Compile_sound`). `encodeTape_eq_cons_of_get_zero`
  is the only encoding fact it needs.
- **`Compile.bitDeciderTM c := composeFlatTM (Compile c) bitTestTM (Compile.exit c)`**
  + `bitDecider_run`: composes `Compile c` with the gadget via `composeFlatTM_run`,
  yielding accept state `1 + (Compile c).states` / reject `2 + …`. Sorry-free
  *modulo* the new `Compile_run_physical`.
- **`Compile_run_physical`** (the one new `sorry`): the compiler's **physical run
  contract** (head rewound to `0`, tape `= encodeTape (c.eval s)`, explicit halt
  step + no-early-halt trajectory, within `overhead`). This is what
  `composeFlatTM_run` needs and what `compileSeq_compose_physical` already
  validates per-fragment — the same gap `Compile_sound` sits behind (Risk **C2**).

In `CookLevin/Complexity/Lang/PolyTime.lean`:

- **`DecidesLang'.toDecidesBy`** / **`DecidesLang'.toInTimePoly`** — the canonical
  decider → `DecidesBy`/`inTimePoly` bridge, via `bitDeciderTM`.
- **`inNPLang_to_inNP`** — the headline: a layer-native NP witness becomes a
  framework `inNP` witness (verifier via `toInTimePoly`, cert relation verbatim).

Framework move in `Complexity/NP.lean`: **`DecidesBy.encode_size` relaxed** from
`≤ size+1` to `≤ 2·size+3` — the layer's `encodeTape ∘ encodeState` is linear but
~2× (from `LangEncodable.enc_size`'s `2·size+1`); all consumers (`proj_left`,
the `verdictTM`/`AllFalse`/`ExistsTrue` deciders) survive. Build green; axioms
clean (only `propext`/`Quot.sound`/`Classical.choice`, plus `sorryAx` from
`Compile_run_physical` on the bridge results).

### What the next agent should pick up

1. **Discharge `Compile_run_physical`** as part of the C1/C2 compiler engineering
   (per-`Op` gadgets + `compileSeq_compose_physical` composition), which also
   discharges `Compile_sound`. This makes the whole decider bridge unconditional.
   (Note: `Compile_polyBound` is now derived from `Compile_sound`, so closing
   `Compile_sound` also closes its corollary.)
2. **Migrate `⪯p` to `polyTimeComputable'`** (ROADMAP step 2): the expensive core
   where S1/S2 stop typechecking. `inNPLang_to_inNP` + `red_inNPLang` are the
   engine for routing `red_inNP` through the layer.
   - **Building blocks landed this pass:** `polyTimeComputable'_id`,
     `polyTimeComputable'_comp_lang` (framework-level helpers via the canonical
     layer), `ReductionWitness'` / `⪯p'` (additive TM-backed reduction types),
     `reducesPolyMO'_to_reducesPolyMO` (`⪯p' → ⪯p`),
     `reducesPolyMO'_reflexive`, `reducesPolyMO'_transitive_lang`,
     `reducesPolyMO'_of_lang`. **Generic `LangEncodable (List α)`** + extra
     instances (`Bool`, `Unit`, `List Bool`) — together they make chain types
     like `cnf = List (List (Bool × Nat))` and `cnf × assgn` derive their
     canonical encoding automatically. Sorry-free modulo `Compile_run_physical`.
   - **Honest TM composition only via the canonical layer.** The framework
     wrapper `polyTimeComputable'_comp_lang` requires the inputs as
     `PolyTimeComputableLang'` (not opaque `polyTimeComputable'`). A purely
     opaque composition is not constructible: the composite's `ComputesBy`
     needs a TM, and a re-encoder between two free-encoding `FlatTM`s does
     not exist in general. This is the structural reason every honest chain
     reduction must be built at the canonical layer first, then bridged.
   - **Strategy** for migrating one reduction in the chain: (a) build the
     canonical-layer witness `PolyTimeComputableLang' f`; (b) lift it to
     `P ⪯p' Q` via `reducesPolyMO'_of_lang`; (c) for now, downgrade with
     `reducesPolyMO'_to_reducesPolyMO` to keep the live `⪯p` chain green
     while the migration progresses incrementally. The first reductions to
     attempt are the **cheap items in the sound tail** (`flatTCC_to_flatCC`),
     not the front of the chain (S1/S2).
3. (Optional) a converse `inNP → inNPLang` is **not** generally possible (an
   opaque `FlatTM` verifier yields no `Cmd`); feed problems in layer-natively
   instead.

The original Task-3 material below is retained for context.

---

## Setup

Build (lake isn't on the MCP/LSP PATH by default):

```
export PATH="$HOME/.elan/bin:$PATH"
lake build                           # whole project
lake build Complexity.Lang.PolyTime  # faster, ~5s after deps cached
```

Build is **green**. ~29 `sorry`s remain (Group C completion gaps), plus the
`sorry`-free *vacuous* S1/S2 defs (invisible to `#print axioms` — see ROADMAP).

**Axiom check** (the lean-lsp MCP cannot find `lake` on its PATH, so use a
scratch file):

```
env LEAN_PATH=$(lake env printenv LEAN_PATH) lean /tmp/chk.lean
```

with `/tmp/chk.lean`:

```lean
import Complexity.Lang.PolyTime
open Complexity.Lang
#print axioms <name>
```

Sorry-free target = axioms are only `propext` / `Quot.sound` (`Classical.choice`
is also acceptable per project policy). **Do not add axioms.**

---

## What was just completed (this branch)

In `CookLevin/Complexity/Lang/PolyTime.lean`:

1. **C5a `map_fst` — both remaining `sorry`s closed** (`normalizes`, `cost_le`).
   `PolyTimeComputableLang'.map_fst` (≈ line 944) lifts `Wf : PolyTimeComputableLang' f`
   to `PolyTimeComputableLang' (fun xc : X × C => (f xc.1, xc.2))`. Two shared
   helper lemmas do the heavy lifting:
   - `PolyTimeComputableLang'.mapFst_pre` (def) — the explicit pre-`Wf.c` state:
     reg `0` = `enc x`, cert `enc c` stashed at reg `k+2`, scratch `[(enc x).length]`
     / `enc x ++ enc c` at `k` / `k+1` (`k = Wf.regBound`).
   - `mapFst_pre_eval` — the 4 unpacking ops (`head`/`tail`/`dropAt`/`takeAt`)
     evaluate `encodeState (x,c)` to `mapFst_pre` (uses `List.take_left`/`drop_left`/
     `tail_cons`/`headD_cons`).
   - `mapFst_pre_agree` — `mapFst_pre` agrees with the clean canonical input
     `encodeState x` on registers `< regBound`, so `Wf.c` runs/costs identically
     there (via `eval_get_of_agree`/`eval_frame`/`cost_agree`).
   - `normalizes` threads the 10-op straight-line program register-by-register;
     `cost_le` reduces the cost to `18 + Wf.c.cost mapFst_pre` then bounds it.
   - **Perf note / lesson:** an early version of `normalizes` named the five
     suffix intermediate states with a `set s6 := …; set s7 := …; …` chain of
     mutually-referencing `let`-bindings. This made `isDefEq`/`kabstract` blow up
     **exponentially** down the chain (~×8 per `set`: 80ms → 660ms → 5.2s → 40s)
     and needed `maxHeartbeats 500000`. The fix: flatten the suffix with a single
     `simp only [Cmd.eval_op, Op.eval]` (keeping only the opaque core `s5` as a
     `set`-local), which drops elaboration to ~0.26s and builds at the **default**
     heartbeat limit. Avoid nested `set` chains over `State.set`/`State.get`
     terms.

2. **`red_inNPLang` no longer takes a `map_fst` hypothesis** (≈ line 1145). It is
   supplied internally by `Wf.map_fst` (a local `let`). Still axiom-clean.

`#print axioms PolyTimeComputableLang'.map_fst` and `... red_inNPLang` both show
only `[propext, Quot.sound]`.

---

## Two hard-won gotchas (you WILL hit these)

1. **`omega` cannot see through `Var := Nat` for *variables* of type `Var`.**
   A universally-quantified register `r : Var` is invisible to `omega` (it
   reports "no usable constraints"). Use explicit `Nat` lemmas: `Nat.ne_of_lt`,
   `Nat.lt_succ_of_lt`, `Nat.pos_of_ne_zero`, `Nat.pos_iff_ne_zero.mp`,
   `Nat.le_of_not_lt`, `Nat.lt_of_lt_of_le`. These apply by defeq (`Var = Nat`).
   `omega` *does* work when the term is genuinely `Nat`-typed (`Wf.regBound`,
   `Wf.regBound + 2`, cost/size bounds) — `Frame.lean` and the `mapFst_pre_*`
   lemmas model this style.
   - **Subtlety:** ascribing a literal as `(0 : Var)` in a `show ... by omega`
     also breaks `omega` (it inserts a `↑` coercion and fails). Write `(0 : Nat)`
     instead — it still unifies with the `Var`-typed `≠` goal by defeq.

2. **`.get` mis-resolves on `State` *literals*.** `([a] : State).get r` picks
   `List.get` (wants a `Fin`) because `State` is `abbrev`'d to `List _`. Write
   `State.get s r` explicitly on literals/ascriptions. (Fine on a plain `State`
   variable or a `Cmd.eval` result.)

Style tip for `Op.eval` reductions: unfold via `simp only [Cmd.eval_op, Op.eval]`
to expose the `State.set`/`State.get` form, then rewrite with
`State.get_set_eq`/`State.get_set_ne` (supply the disequality explicitly, not via
a postponed `by omega` whose metavariables aren't resolved yet).

---

## The next task — Task 3: the framework decider bridge `inNPLang Q → inNP Q`

This is the **one remaining obligation** to route `red_inNP` through the layer.
Its core is the `sorry` **`DecidesLang.toDecidesBy`** (`PolyTime.lean` ≈ line 84):

```lean
theorem DecidesLang.toDecidesBy {X} [encodable X] {P} {costBound}
    (D : DecidesLang P costBound) (h_mono : monotonic costBound) :
    Nonempty (DecidesBy P (fun n => Compile.overhead (2 * costBound n)))
```

### The obstruction (precise)

- `DecidesLang`/`DecidesLang'` programs write the yes/no answer to **register 0
  / tape 0** (`[1]` = accept, `[0]` = reject; see `State.isAccept`/`isReject`).
- `DecidesBy` (`NP.lean` ≈ line 51) reads its answer from the TM **state index**:
  `decides_pos`/`decides_neg` require reaching distinct halting states
  `cfg.state_idx = acceptState` / `= rejectState`.
- `Compile c` always halts in a **single** exit state with the answer on the
  **tape**. So you must run a **tape→state branch gadget** ("C6 bit test") after
  `Compile c`: read register 0, halt in a distinct accept vs reject state.
  `Compile_sound` alone does **not** suffice.

### What already exists (proven, sorry-free) vs what's missing

| Piece | File:line | Status |
|---|---|---|
| `FlatTMConfig`, `runFlatTM`, `stepFlatTM`, `haltingStateReached`, `initFlatConfig` | `MachineSemantics.lean` | ✅ proven |
| `runFlatTM_extend` (budget padding), `runFlatTM_compose` | `MachineSemantics.lean` | ✅ proven |
| `composeFlatTM` + `_valid` + `_run` (sequential composition) | `TMPrimitives.lean` ~80 | ✅ proven |
| `branchComposeFlatTM` + `_valid` + `_run_pos`/`_run_neg` | `TMPrimitives.lean` 1133 / 2232 | ✅ proven |
| `BranchTester` structure (the gadget interface) | `Compile.lean` 492 | exists |
| `compileTestBit` (the gadget) | `Compile.lean` 530 | ❌ **stub** (`branchTester_default`: 2 states, empty `trans`, nothing halts) |
| `compileIfBit` (uses the tester + `branchComposeFlatTM`) | `Compile.lean` 584 | ✅ assembled (proof `compileIfBit_sound` is `sorry`) |
| `Compile_sound` | `Compile.lean` 1150 | ❌ `sorry` (the project instructs treating it as an assumed in-scope theorem) |
| `DecidesLang.toDecidesBy` | `PolyTime.lean` 84 | ❌ `sorry` (this task) |
| `inNPLang Q → inNP Q` | — | ❌ not yet stated |

### Recommended plan for Task 3 (probe first, then build)

The handoff before this one flagged C6 as "feasible but expensive — budget a
probe first." The exploration confirms it is a self-contained TM construction.
Suggested decomposition:

1. **Build a real `compileTestBit 0`** (or a dedicated `tapeBitToState` gadget):
   a small `FlatTM` over the `Compile.encodeTape` format (registers shifted `+1`,
   `0`-delimited, terminated by `endMark = 3`) that reads register `0`'s first
   symbol and reaches `exitPos` (bit `1`) vs `exitNeg` (bit `0`), distinct states.
   Prove its `runFlatTM` behavior as a standalone lemma — this depends **only** on
   the encoding format, **not** on `Compile_sound`, so it is cleanly isolable.
   (Reuse `BranchTester`'s contract; `compileIfBit`/`branchComposeFlatTM` show the
   shape.)
2. **Compose** `Compile D.c` then the gadget with two **immediate-halt** branches
   (trivial 1-state halting machines for accept/reject) via `composeFlatTM` /
   `branchComposeFlatTM`. Use `composeFlatTM_run` + `branchComposeFlatTM_run_pos/neg`
   + `runFlatTM_extend` for the budget. The budget `Compile.overhead (2·costBound n)`
   already has headroom over `Compile.overhead (sizeIn + cost)` (cf. the existing
   `toFrameworkWitness'` budget algebra around `PolyTime.lean` line 218).
3. **Assemble `DecidesLang.toDecidesBy`** from `Compile_sound` (assumed) + the
   gadget's run lemma: `Compile_sound` gives the tape = `D.c.eval (encodeIn x)`,
   whose reg 0 is `[1]`/`[0]` by `D.decides`; the gadget converts that to the
   accept/reject state index.
4. **Then** add a `DecidesLang'.toDecidesLang` (canonical→free-encoding, easy —
   mirror `PolyTimeComputableLang'.toLang` ≈ line 578) and assemble
   `inNPLang Q → inNP Q` (destructure `InNPWitnessLang`, bridge its `verifier :
   DecidesLang'` to `inTimePoly` via `toDecidesBy` + `inTimePolyLang_to_inTimePoly`,
   keep `rel_correct` verbatim).

Estimated effort: substantial (the C6 gadget + its run proof is the bulk). The
gadget proof is independent of the `Compile_sound` `sorry`, so it can land
cleanly on its own even before `Compile_sound` is discharged.

---

## After Task 3 (the rest of the S3 migration)

Per ROADMAP *The plan from here*, step 2:

1. **Migrate `⪯p` to `polyTimeComputable'`.** Swap `ReductionWitness.reduction_poly`
   from `polyTimeComputable` to the TM-backed `polyTimeComputable'`
   (`PolyTime.lean` ≈ line 195). `polyTimeComputable'_to_polyTimeComputable`
   (line 203) keeps every size-bound lemma in `NP.lean` valid verbatim. **This is
   the expensive core**: it is precisely where S1 (the if-on-the-answer reduction)
   and S2 (the dummy bridges) **stop typechecking** — building honest witnesses
   there is the real work (Cook 2D tableau for S1; collapse phantom bridges for
   S2). Expect the conditional `CookLevin` theorem to break here until those are
   honest.
2. **Ripple the sound tail.** `flatTCC_to_flatCC` etc. are cheap;
   `BinaryCC_to_FSAT`/Tseytin is the expensive tail item. The tail
   (`FlatTCC → … → SAT`) is genuine mathematics — do not touch its content, only
   re-thread the witness type.

---

## Conventions

- Commit per logical step with a **green build**; record gaps in commit messages.
- Keep `README.md` + `CookLevin/ROADMAP.md` updated.
- Prefer `def` + `sorry` over `axiom`; decompose `sorry`s (each split is a
  structural decision) rather than elaborating them.
- `#print axioms` on new results: only `propext` / `Quot.sound`
  (/ `Classical.choice`). **No new axioms.**
