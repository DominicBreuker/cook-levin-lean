# Handoff — the working plan for both streams

Authoritative status & the full risk register live in [`../README.md`](../README.md)
and [`ROADMAP.md`](ROADMAP.md). This file is the forward-looking working plan; we
work **multi-session in two alternating streams** — at the start of each session
the owner says **`bottom-up`** (build the gadgets/lemmas the contracts need) or
**`top-down`** (work the final assembly, surface gaps early, `sorry` what is
reasonably provable).

**Read in this order.** "Where the proof stands" → "★ Latest session" → the
**NEXT** section for your stream. Everything from "Locked invariants" down is a
**reference index**, not narration: consult it before building anything, do not
read it front to back.

## Where the proof stands (2026-07-26-b)

**The sound tail: COMPLETE & axiom-clean.**
`FSATSATComp.flatTCC_to_SAT_reducesPolyMO' : FlatTCC ⪯p' SAT` — the whole chain
`FlatTCC → FlatCC → BinaryCC → FSAT → SAT` as ONE composed free witness.

**The front (C8-0…C8-4): COMPLETE & axiom-clean.**
`Complexity.Lang.FrontWitness.front_reducesPolyMO' : Q ⪯p' FlatSingleTMGenNP`
for any `W : InNPWitnessLangFreeSplit Q`. Consume it, `WQ` and `fQ_correct` as
black boxes — do not re-derive the front.

**S1 — the last gap, THE CRITICAL PATH.** The program is ASSEMBLED
(`Reductions/S1Program.lean`); **stage C, stage M-yes and the cost ladder are
all that is left.**

| piece | status |
|---|---|
| tableau mathematics (`Simulators/CookTableau.lean`, `GuessTableau.lean`) | ✅ sorry-free, axiom-clean, incl. both size bounds |
| reduction map + guard + correctness iff + output bound (`Reductions/S1Map.lean`) | ✅ axiom-clean |
| witness fields (layouts, `s1Key_injective`, `encodeIn_size`, `computes`, `usesBelow`, `decode_agree`) (`Reductions/S1Witness.lean`) | ✅ all proven; only `cost_le` open |
| program stages **P** (parse) + **G** (guard) (`Reductions/S1Parse.lean`) | ✅ axiom-clean |
| stage C's pure model + `normTrans` spec + stage **M-no** (`Reductions/S1Cards.lean`) | ✅ sorry-free, axiom-clean |
| the atom `emitBlk` + stages Σ / I / F (`Reductions/S1Emit.lean`) | ✅ sorry-free, axiom-clean |
| **the program `s1Program` + `computes` (both branches) + `usesBelow`** (`Reductions/S1Program.lean`) | ✅ **NEW (2026-07-26-b)**; no-branch axiom-clean, yes-branch modulo the two stages |
| **stage C (the card emitter)** — model proven, contract pinned, `Cmd` unwritten | ❌ open, the big one |
| **stage M-yes** (`1^(steps+1)` + five copies) — contract pinned | ❌ open, half a day |
| the whole-program cost ladder (`cost_le`) | ❌ open, LAST |

When they land, two seams close
`Q ⪯p' FlatSingleTMGenNP ⪯p' FlatTCC ⪯p' SAT` = `NPhard'' SAT`: **C8-5**
(`W_Q` → S1, `mfc` drops `W_Q`'s extra unary size register) and the **fourth
tail seam** (S1 → the sound tail), a **pure register scrub**.

**Sorries in built code: 12** — five pre-existing (`red_inNP`'s `inTimePoly`
half in `NP.lean`; `hasDeciderClassical` in `GenNP_is_hard.lean`; 3×
`MultiToSingle`, dead code); six in `S1Program.lean` (`stageC` / `stageC_run` /
`stageC_usesBelow`, `stageMYes` / `stageMYes_run` / `stageMYes_usesBelow` — only
the two `def`s are real gaps, the four theorems are their contracts); and
`S1Witness.s1_reductionLang.cost_le`. The rise from 6 is a **decomposition, not
a regression** (methodology 3): one opaque `s1Program` marker became six
*contracts that the assembly already consumes and typechecks against*.
`S1Parse.lean`, `S1Cards.lean` and `S1Emit.lean` stay sorry-free. The headline
`CookLevin`'s `sorryAx` is unchanged and still wholly hardness-side.

## ★ Latest session

**2026-07-26-b (top-down) — the PROGRAM IS ASSEMBLED. `computes` is proven:
the guard-false half outright and axiom-clean, the yes-branch half modulo only
`stageC_run` and `stageMYes_run`. `usesBelow` and `decode_agree` are closed too,
so `S1Witness.s1_reductionLang` is down to ONE open field, `cost_le`.**

New file `Reductions/S1Program.lean` (~430 LOC), new probe
`probes/S1ProgramProbe.lean` (all green). `S1Witness.lean` now imports the
program (the dependency used to point the wrong way); `s1Key` / `s1Extract` /
`SIGMA`…`STEPS` / `s1RegBound` **moved to `S1Program`** — update any reference.
`Complexity.lean` imports `S1Program` (do not forget this for new modules).

**Endpoints to consume — the program and its contracts:**

* **`S1Program.s1Program`** `= S1Parse.stagePG ;; Cmd.ifBit S1Parse.FLG
  yesBranch S1Cards.stageMNo`, `yesBranch = stageSig ;; stageInit ;; stageC ;;
  stageFin ;; stageMYes` (suffix defs `ySuf1/2/3` for peeling).
* **`S1Program.s1Program_computes`** — the witness's `computes` field, already
  wired into `s1_reductionLang`. Its two halves: **`noBranch_computes`**
  (axiom-clean, quantified over an ARBITRARY yes branch) and
  **`yesBranch_run`** (modulo the two stage contracts).
* **`S1Program.stageC_run` / `stageMYes_run`** — ⚠ **the two contracts the next
  bottom-up session must MEET, not restate.** They are the interface; changing
  either re-opens `yesBranch_run`.
* **`S1Program.EScratch` / `CDirty`** + `ne_of_not_scratch` / `ne_of_not_cdirty`
  + **`stageSig_frame` / `stageInit_frame` / `stageFin_frame`** — the coarse
  frame predicates. `EScratch` = `[37,48) ∪ {HEAD, INBLK, SKIPR}` is *exactly*
  what Σ/I/F dirty besides their own output (this is proven, not assumed);
  `CDirty` = `EScratch ∪ {EOUT_C} ∪ [14,32)` is stage C's licence. **Every new
  stage should state its frame this way** — one hypothesis per stage instead of
  fourteen.

⚠ **FINDING A (a `sorry` in a `def` poisons the STATEMENT of every lemma about
it).** `s1Program_computes_neg`'s proof is complete, yet `#print axioms` lists
`sorryAx` — because `s1Program` appears in its *statement* and contains
`stageC`. The fix is to quantify over the placeholder: `noBranch_computes` takes
the yes branch as a parameter `(yes : Cmd)` and *is* axiom-clean. **Do this for
every skeleton-phase lemma whose content is independent of the open piece** —
otherwise `#print axioms` cannot distinguish "proof incomplete" from "mentions
an unbuilt program", and the project's main soundness instrument goes blind.

⚠ **FINDING B (`#eval` refuses ANY expression reaching a `sorry`, even down an
untaken branch).** `#eval (s1Program.eval …)` aborts on the guard-FALSE input,
although `Cmd.ifBit` never forces `yesBranch`. So a skeleton program cannot be
probed end to end at all: probe the branch composition the proof reduces to
(`probes/S1ProgramProbe.lean` §2 runs `stagePG ;; stageMNo`) and re-point the
probe once the placeholders land.

⚠ **FINDING C (the sorried contracts are the new risk surface — probe them).**
A `sorry`-ed `_run` lemma can be stated *wrongly* and the assembly still
typechecks, so `probes/S1ProgramProbe.lean` §3–4 checks the two contracts
numerically on the real frozen head layout: after `stagePG ;; stageSig ;;
stageInit ;; stageFin`, the registers `EOUT_S`/`EOUT_I`/`EOUT_F` equal entries
`1`/`2`/`4` of `s1Key (guessTableau …)`, register `4` still holds `1^steps`, and
`encNats (cardBlocks M)` equals entry `3`. All green. **Any change to either
contract must re-run this probe.**

⚠ **FINDING D (measured: stage C is ~1700× the rest of the output).** On the
probe's instances the five output registers are
`(22, 76…270, 132051 / 442667, 30…116, 1…4)` cells. The card register is
`>99.8%` of the emitted output on every instance — so the cost ladder is
**stage C's ladder plus rounding**, and no effort spent optimising Σ/I/F/M can
matter. (It also means `#eval` of a *complete* `s1Program` will be slow; probe
bridges, not end-to-end runs, on anything larger than these.)

⚠ **FINDING E (`CDirty` includes `S1Parse.FLG = 17` — deliberately).** Stage C
may clobber the guard flag: `Cmd.ifBit` reads its test register *before*
entering the branch, so nothing downstream re-reads `FLG`. This is what lets
stage C treat the whole P/G scratch block `[14,32)` as free.

**Earlier, still binding (2026-07-26, the emitter stages).**

* **`S1Emit.emitBlk cnt src dst`** + `emitBlk_run` / `emitBlk_cost`
  (`≤ 3 + 5v + v²`) / `emitBlk_usesBelow` — appends `FlatTCCFree.encNat v
  = 1^v 0` reading `v` as `|src|`. Register-generic. **Every large output is
  built with this.**
* **`S1Emit.loadSg` / `loadSg_run`** — `ESG := 1^(Sg M)` off `PSIG`/`PSTATES`,
  the program's only multiplication, paid once outside every loop.
* **`S1Emit.stageSig` / `stageSig_run` / `stageSig_usesBelow`** —
  `EOUT_S = 1^(PSg M)`.
* **`S1Emit.stageFin` / `stageFin_run` / `stageFin_usesBelow`**, with the model
  `finBlocks` + **`finBlocks_eq`** — `EOUT_F = encFinal (flattenFinal
  (guessFinal M))`.
* **`S1Emit.stageInit` / `stageInit_run` / `stageInit_usesBelow`**, with the
  models `cellsA`/`cellsB`/`cellsC`/`initBlocks` + **`initBlocks_eq`** —
  `EOUT_I = encNats (flattenString (preludeRow M s maxSize steps))`.
* Reusable inside stage C: **`repOne`**, **`iniCellK` / `iniLoopK_run`** (a
  constant-value cell in a loop, with an optional first-iteration bonus),
  `encNats_singleton`, `encFinal_append`, `encFinal_singleton`,
  `drop_getElem_cons` / `tail_drop_succ` / `getD_of_le` / `encSyms_len_ge`.

(The 2026-07-26 size-bound finding — a fixed-size header forces an additive term
— is now a **locked invariant**, see below.)

⚠ **FINDING 2 (stage F needs NO validity hypothesis).** `cookFinal` runs `q`
over `[0, states]` and asks `M.halt.getD q false`; the emitter drains `PHALT`
one `head` cell per `q`, and a drained-empty `head` yields `[]`, which `ifBit`
reads as *false* — exactly `getD`'s out-of-range value. So the `|halt| = states`
guard conjunct is not needed by F on any machine (probe covers a machine whose
halt list is shorter than `states`).

⚠ **FINDING 3 (the emitter template stage C must copy).** `hv sig q b
= (sig+1)(q+1) + b` is **never multiplied inside a loop**: one register holds
`1^((sig+1)(q+1))` and grows by `1^(sig+1)` per `q` iteration, and `b` is *the
inner `forBnd`'s own counter register*. The innermost body is then two
`tallyReg`s plus three constant appends. **Every one of stage C's seven families
has this shape** — a product of loop indices is an incrementally maintained
register plus the innermost counter.

⚠ **FINDING 4 (stage I is three consecutive loops, not one branching loop).**
`pKindAt`'s positional case split *partitions* the row, so the emitter is three
sequential loops bounded by registers that already hold those lengths (reg `2`,
reg `3`, reg `4`+3) — no on-machine comparison of the position against anything.
The only positional datum left is "is this the row's first cell": one flag
register (`EE`) cleared by the first cell emitted. Loop A is **idle-tolerant**
(`S1Parse.sLoop`'s pattern) because the layer has no "number of items in a
sentinel stream" register to loop on.

⚠ **FINDING 5 (the guard is load-bearing, not a convenience).** Stage I does not
test `s[p] < sig` — under `list_ofFlatType M.sig s` that branch is unreachable.
`probes/S1EmitProbe.lean` exhibits an **off-guard** instance (`M.sig = 0`,
non-empty input) where the emitter and `preludeRow` genuinely disagree. This
confirms design decision 1 (everything under one `Cmd.ifBit S1Parse.FLG`) is
required for correctness, not just for cost.

**The emitter register frame — PINNED (`Reductions/S1Emit.lean` docstring).**

```
32 EOUT_S  Σ's output (1^PSg)     37 ESG  1^(Sg M)     43 EJ1  loop counter
33 EOUT_I  I's output             38 EA   scratch      44 EJ2  loop counter
34 EOUT_C  C's output (stage C)   39 EB   scratch      45 EJ3  loop counter
35 EOUT_F  F's output             40 EC   scratch      46 EK1  scratch
36 EOUT_T  1^(steps+1) (stage M)  41 ED   scratch      47 EK2  scratch
                                  42 EE   scratch
```
`32`–`36` persist to stage M; `37`–`47` are scratch every stage reuses. Nothing
here touches `0`–`13` (stage P's outputs and the head layout) — each stage's
`_run` carries an explicit frame clause saying so, and the probe checks it by
`#eval` on registers `0`–`13`.

**Earlier, still binding (2026-07-25-c, stage C's model).** `S1Cards.cardBlocks_eq`
/ `encCards_eq` (stage C's target is seven `List.range` streams with one proven
equation per family), `normModel_eq` (the `normTrans` dedup is a three-number
key pass plus one `PHALT` bit lookup), `stageMNo` (the guard-false branch), and
its three findings: the prelude family is **`Θ(σ³)`, not `Θ(σ⁶)`**; **never
`concat` onto an output register** (`Op.cost concat` charges the whole
destination) and a unary block of value `v` costs `Θ(v²)`; and **`cost_bound` is
a free polynomial** — raise it rather than contort the emitter (it must keep
dominating `S1Map.s1Map_size_le`, that is its only constraint).

**Earlier, still binding (2026-07-25-b, stages P+G).** `stagePG_run` leaves
`1^sig`, `1^tapes`, `1^states`, `1^start`, `1^|halt|`, the halt **bit list**,
`1^|trans|` and `encSyms (transFlat M)` in registers `6`–`13` and
`FLG = if S1Map.s1GuardB M s then [1] else []` in register `17`, register `0`
empty; plus `stagePG_usesBelow : UsesBelow stagePG 32` and `stagePG_frame`
(registers `1`–`5` untouched). Its findings that still constrain new work:

1. **P+G are cubic**, so the parse is not the budget driver — do not optimise it.
2. **The parse never desynchronises, on any machine** (`flattenEntry` writes each
   list's own length before its payload), so P/G take no validity hypothesis.
3. **`CliqueRelTM.readNum`/`ltBit` are reused verbatim**, so registers `15`
   (`HEAD`), `16` (`INBLK`), `22` (`LT_B`), `26` (`SKIPR`) are RESERVED for the
   whole S1 program.
4. **`forBnd` samples its bound register's length ONCE at entry**, so a loop may
   overwrite its own bound.
5. **`PHALT` (register 11) is a RAW BIT LIST** `M.halt.map bitOf`.
6. **The suffix-peel proof shape**: name every command suffix and peel with
   `rw [Cmd.eval_seq]`, never `rfl`; each register a suffix does not write is
   then ONE `Cmd.eval_get_of_not_writes` (`by decide` on the write set).

**The S1 register frame — PINNED (`Reductions/S1Parse.lean` docstring).**

```
0  ZERO (andIn no-op target; ends [])   6  PSIG      12 PNTRANS   17 FLG
1  MREG (in) / SIGMA (out)              7  PTAPES    13 PTRANS    18 VAL
2  SREG (in) / INIT  (out)              8  PSTATES   14 SCAN      20 RES
3  1^maxSize (in) / CARDS (out)         9  PSTART    15 HEAD  ⊘   21 ONE
4  1^steps   (in) / FINAL (out)        10  PNHALT    16 INBLK ⊘   23 TSCAN
5  STEPS (out)                         11  PHALT     22 LT_B  ⊘   24 NEF
                                                     26 SKIPR ⊘   27–31 I1–I5
19, 25 free · 32–47 the emitter frame above · s1RegBound = 48
```

## ★ Earlier sessions — the findings that still constrain new work

Everything durable lives in "Proven, reusable", "Locked invariants" and
"Conventions"; git history has the narration. Kept here only where a *finding*
still binds.

- **2026-07-26 (bottom-up)** — the emitter atom `emitBlk` and stages Σ / I / F
  (`S1Emit`), plus `flattenTM_size_le` (found FALSE as stated and corrected);
  its findings are under "★ Latest session" above.
- **2026-07-25-c (top-down)** — stage C's pure model (`S1Cards`), the `normTrans`
  spec and stage M-no; its three findings are under "★ Latest session" above.
- **2026-07-25-b (bottom-up)** — the S1 program's stages P + G; its six binding
  findings are listed under "★ Latest session" above (they still govern every
  new stage).
- **2026-07-25 (top-down)** — the S1 map + witness skeleton, and the
  `encodable FlatTM` correction (see "Locked invariants": an `encodable.size`
  that merely *counts* a structure is not honest if some witness must *spell it
  out*; ask this of every new type).
- **2026-07-24-c (bottom-up)** — both S1 size bounds (`≤ (2·(b+1))^10`) + the
  reusable `encodable.size` toolkit. ⚠ the enlarged base is **not** optional: a
  `C·b^d` collapse overshoots a tight `n^10` at small `n` (`guessTableau` of the
  trivial machine has size `2731 > 1024`), and guess's base **includes
  `maxSize`**. Numerics: `probes/SizeBoundProbe.lean`.
- **2026-07-20…-c (bottom-up)** — C8-4's three pieces. ⚠ **still binding**: the
  `tallyCells` monomial argument **cannot** discharge `fQ_correct`'s
  `hmax`/`hsteps` (the tally only bounds `size x` from *above*), so
  `W_Q.encodeIn x := encX x ++ [1^(size x)]` carries a unary size register —
  which is exactly what C8-5's `mfc` must drop. `tallyCells` is UNUSED.
- **2026-07-17…-d (top-down ×3)** — the S1 v2 redesign. Two machine-checked
  defects were found *before* effort was spent: non-local zero-padding
  jump-writes (⇒ the append-only frontier semantics) and the **phantom head** at
  the right row edge (⇒ the right boundary marker + `copyRightCards`). Both are
  now locked invariants.
- **2026-07-02…-16** — the free line (`SeamData`/`comp`,
  `reducesPolyMO'_of_langFree`), the C8 framework batch, the compiler
  completion (C2), Part 0.1 (the encodable sweep), and the whole sound tail with
  its three live seams.

**Final tail exit layout** (2026-07-16; what the ENDPOINT bridge sees from the
composed `flatTCC_to_SAT_witness`, `regBound = 57`): **reg 1 =
`replicate |N| 1`, reg 2 = `encodeCnf N`** — the SAT verifier's
`CLAUSE_TALLY`/`CNF_STREAM` layout, by design (`decodeOut = invFun encodeCnf`
on reg 2); reg 0 = `serF f` (the intermediate formula, preserved); `buildSAT`
scratch 3–26 dirty; regs 27–56 hold the LEFT composite's residue (the last
seam's `scrub3` deliberately does not touch them — outside the right frame 27);
regs `≥ 57` read `[]`.

## The free line — the working architecture (use this, and only this)

- **Verifiers**: free `DecidesLang` with bespoke bit-level `encodeIn`
  (numbers UNARY) → `DecidesLang.toDecidesBy`/`toInTimePoly` (live:
  `evalCnfDecidesLang`, `cliqueRelDecidesLang`).
- **NP witnesses**: `InNPWitnessLangFree`/`inNPLangFree` (+ `inNPLangFree_to_inNP`).
- **Reductions**: free `PolyTimeComputableLang` → `toFrameworkWitness'`/
  `reducesPolyMO'_of_langFree`; verifier precomposition via
  `DecidesLang.FreePrecomposeData`/`red_inNP_of_langFree`; **witness-witness
  composition via `SeamData`/`comp` — LIVE THRICE, stacking on composed
  witnesses** (`FlatTCCBinComp.flatTCC_to_binaryCC_seam` →
  `BinaryCCFSATComp.binaryCC_to_FSAT_seam` → `FSATSATComp.fsat_to_SAT_seam`
  — the models for every next seam, incl. both frame-mismatch variants:
  wider right frame = length argument; narrower right frame = no scrub
  above it).
- **Templates for new reduction witnesses** — copy these, not first principles:
  - `NP/kSAT_to_SAT_free.lean`: re-encoder + reduction sharing one program,
    fold invariants, tight `encodeIn_size`, `FreePrecomposeData`.
  - `Reductions/FlatTCC_to_FlatCC_free.lean`: the sound-tail unguarded-map
    pattern (backward validity transfer + unconditional iff), shared-layout
    registers, `blockMove`/`halfMove` stream re-formatting, `encSList`
    prefix-free injectivity, multi-field decode via `Function.invFun encKey`.
  - `Reductions/FlatCC_to_BinaryCC_free.lean`: **the guarded-map pattern** —
    on-machine validity flag (`allLtB` reflection ↔ `isValidFlattening` via
    `validB_iff`), guard branch to the no-instance, the item view of sentinel
    streams (`encItems`/`expandItems` — ONE loop lemma for cards+final via a
    shared scratch output `BOUT` + copy-out), unary multiplication
    (`mulLoop_run`), truncated-subtraction compare.
  - `Reductions/FlatTCC_to_BinaryCC_comp.lean`: **the seam pattern** — scrub
    `mfc`, `interval_cases`-bridge over the frame, constant seam budget.
  - `Reductions/BinaryCC_to_FSAT_comp.lean`: **the stacked-seam pattern** —
    seam on a COMPOSED left witness (unfold its `.c` with one `heval`, push
    the previous seam's bridge through with `Cmd.eval_agree`), the
    wider-right-frame close (registers above the left frame via
    `Cmd.eval_length_le` + `get_nil_of_len_le`), local `binConvert_key`
    extraction of the predecessor's exit key.
  - `Reductions/FSAT_to_SAT_comp.lean`: **the narrow-right-frame seam** —
    when the right witness's frame is NARROWER than the left composite's,
    the bridge only quantifies below the right frame, so `mfc` scrubs only
    registers inside it and the left residue above needs NO handling; the
    right `encodeIn`'s missing registers read `[]` and close by `rfl`.
    Probe: `probes/SATSeamProbe.lean` (decode the machine's own intermediate
    stream with `decodeF` instead of cloning noncomputable maps; check
    bridges — not end-to-end `#eval` — on >1K-bit instances).
  - `Reductions/FSAT_to_SAT_free.lean` + `NP/FSAT_to_SAT_pre.lean`: **the
    tree-traversal pattern** — a TREE-typed *input* consumed by one forward
    token scan of its Polish serialization: positional fresh variables
    (`b + token index`, base `b := stream length`), right-child recovery by
    the arity-budget scan (`subtreeScan`), and a Lean-side positional
    equivalent (`ptseytin`) proven correct where recursion is free. **The pure
    scan model (`budgetStep`/`subtreeTok`/`scanClauses`/`mScan`) is PROVEN =
    the tree map** (`mScan_eq_fsatToSat`, via `subtreeTok_serF` +
    `scanClauses_serF`) — the template for "prove the machine folds compute a
    pure model, then close with the model≡tree equivalence" (factors the tree
    recursion off the machine proof). The core budget-scan invariant
    (`budgetStep_iterate_subtree`: processing `serF g`'s tokens pays off one
    budget obligation) + the freeze lemma are reusable for any prefix-parse
    counter.
- **The canonical `LangEncodable` layer stays DEAD** (generic product encoding
  is size-unsound — `probes/UnaryProductSizeProbe.lean`). Do not rebuild it.

### ⚠ Standing architecture risks — check every new witness against these

1. **Honesty is per-witness discipline, not enforced.** `eIn`/`encodeIn` must
   be the natural layout of the *input* (never of `gmap v`), `decodeOut` the
   inverse of the natural *output* layout, all reduction work in the `Cmd`.
   The trivial dishonest instantiation satisfies every field — review each
   witness. (Shared-layout registers for identity fields are fine.)
2. **Seam discipline**: pin each new witness's input layout to its
   predecessor's exit frame and document the exit layout (dirty registers
   included) for the successor. The chain-head layout is **FROZEN
   (2026-07-18, `Reductions/HeadLayout.lean`)** — `headEncodeIn`
   (`headRegBound = 5`) + the `headEncodeIn_bitState` certification; the
   S1 witness's `encodeIn` MUST be it and C8-5's seam MUST hit it. Do not
   change it without re-running `probes/C8SeamProbe.lean` and updating both
   build plans.
3. **Guard-or-no-guard is a per-step decision**: probe invalid→invalid ON
   PAPER before coding (counterexample method: pick a tiny invalid instance,
   check whether its image is accidentally wellformed+satisfiable).
4. **The front instance types are size-MEASURED, not string-encodable**
   (Part 0.1 finding): `GenNPInput.rel` / `mTMGenNPFixedInput.accepts` /
   `TMGenNPFixedInput.accepts` are abstract predicates, so their
   `encodable.size` counts only the data fields (tapes + the two numeric
   parameters). That is honest for `⪯p` size bounds, but **no TM can consume
   these types as inputs** — C8 retires the abstract front entirely (scoped
   2026-07-04: per-`Q` witnesses target corrected `FlatSingleTMGenNP`
   directly). Never add a size-0 instance to "fix" a missing-instance error;
   the fallback was deleted deliberately.
5. **`encodable.size` must DOMINATE the register content, not merely count the
   structure (2026-07-25 S1 finding).** A size that counts a container's
   *elements* but not their *payloads* is honest for `⪯p` output-size bounds
   yet makes `encodeIn_size` unsatisfiable for any witness that must spell the
   value out on tape — exactly what killed `sizeFlatTM` (flat `5` per
   transition entry) once the S1 witness had to emit `encSyms (flattenTM M)`.
   For every new type ask: *does some witness have to write this structure out
   cell by cell?* If yes, the size must be the data-field sum. Same check for
   any new `encodeIn` against an existing type's size.
6. **The hypothesis side of hardness is dishonest-capable too (C8 finding
   F1).** `inTimePoly`/`inNP` are classically TRUE for every predicate (the
   cheating `DecidesBy.encode`), so any `∀ Q, inNP Q → …` hardness statement
   is unprovable-honestly by construction. Quantify hardness over free-line
   verifier witnesses (`NPhard''` over `InNPWitnessLangFreeSplit`, C8-0/C8-1)
   and never "fix" a hardness obligation by strengthening only the
   conclusion side.

---

## C8 — the honest universal front: DONE (C8-0…C8-4), C8-5 waits on S1

The per-`Q` front is built and axiom-clean. What a future session needs:

- **The endpoint to consume:** `Complexity.Lang.FrontWitness.front_reducesPolyMO'
  : Q ⪯p' FlatSingleTMGenNP` for any `W : InNPWitnessLangFreeSplit Q`, together
  with `WQ` (the `PolyTimeComputableLang` witness) and `fQ_correct`. **Black
  boxes — do not re-derive the machine, the lifting or the program.** Artefact
  lists are in "Proven, reusable".
- **C8-5 (the seam) — the only C8 item left**, and it is now *small*: a fourth
  `SeamData`/`comp` joining `WQ` to the S1 witness on the frozen
  `HeadLayout.headEncodeIn` (`headRegBound = 5`). `mfc` drops `W_Q`'s extra
  unary size register (scratch `≥ headRegBound`) and is otherwise the identity
  onto `headEncodeIn`. **No longer blocked** — `s1_reductionLang` exists with
  `usesBelow`/`decode_agree` proven, and the seam's `bridge` is a frame argument
  that does not care whether stage C is a placeholder. Write it now.
- **Why hardness is quantified over free-line verifier witnesses (finding F1 —
  still binding).** `inTimePoly P` is classically TRUE for *every* predicate
  (the cheating `DecidesBy.encode`), so `∀ Q, inNP Q → …` quantifies over
  undecidable predicates and can never be honest. Hence `NPhard''` over
  `InNPWitnessLangFreeSplit` (Cert `= List Bool`, split pair layout, `encX`
  size bound). Never "fix" a hardness obligation by strengthening only the
  conclusion side. Do **not** close `hasDeciderClassical` with the cheating
  encoder — that `sorry` is the honest marker of the open hardness half.
- **Endgame note (off the critical path).** The live SAT verifier does not
  factor verbatim as a Split witness: `assgn` certs are `List Nat`
  (sentinel-unary) and `encodeState` has 8 trailing scratch `[]`s after the cert
  register. The adaptation (trailing-`[]` trim + a bits→sentinel decode-prefix
  `Cmd`, as a `DecidesLang.FreePrecomposeData`) is needed for the in-NP half of
  `NPcomplete'' SAT`, not for hardness.
- **After S1 + C8-5**: swap the headline to `NPhard''`/`NPcomplete''` over the
  composed front+tail chain and delete the legacy `⪯p` front (that IS the S2
  collapse; `Simulators/MultiToSingle.lean` is already dead code).

## NEXT TOP-DOWN session — the two seams (start them NOW, in skeleton form)

Items 1–3 of the previous plan are DONE (`Reductions/S1Program.lean`: the
assembly, the coarse frame predicates, both halves of `computes`). The witness
is down to `cost_le`, and the seams are the next structural risk. **Both seams
can be written as skeletons today**, against `s1_reductionLang` as it stands —
their `bridge` fields are frame arguments over `s1Program_usesBelow`, which does
not care that stage C is a placeholder. Do that *before* stage C lands: a seam
that needs a different exit layout is a change to `s1Key`, and `s1Key` is what
the whole yes branch is now proven against.

1. **The fourth tail seam — `Reductions/S1_to_FlatTCC_comp.lean` (do this
   first).** `SeamData s1_reductionLang FSATSATComp.flatTCC_to_SAT_witness`;
   `mfc` is a **pure scrub** of register `0` and every S1 scratch register in
   `[6, 57)`; `bridge` is `AgreeBelow 57`; the right `encodeIn` **is**
   `FlatTCCFree.encodeIn` (`rfl` — that is the whole point of `s1Key`).
   Template: `Reductions/FSAT_to_SAT_comp.lean` (narrow-right-frame variant),
   with `Reductions/FlatTCC_to_BinaryCC_comp.lean`'s `scrub` for the `mfc`.
   ⚠ The bridge needs registers `≥ 6` of the exit state to read `[]`. Stage M-no
   leaves the emitter registers `[32,48)` dirty and P/G leaves `[6,31]` dirty, so
   **the scrub must clear all of `[6,48)` on BOTH branches** — check this against
   `s1Program_usesBelow` (`48`), not against a per-branch analysis.
   ⚠ Register `0` ends `[]` on the no-branch (`stagePG_run`) but is *not* claimed
   empty on the yes-branch — scrub it unconditionally.
2. **C8-5** — `SeamData WQ s1_reductionLang` on the frozen
   `HeadLayout.headEncodeIn` (`headRegBound = 5`); `mfc` drops `W_Q`'s extra
   unary size register (scratch `≥ headRegBound`) and is otherwise the identity.
   Same "write it now, it does not depend on stage C" argument.
3. **Then the endpoint**: with both seams, `Q ⪯p' FlatSingleTMGenNP ⪯p' FlatTCC
   ⪯p' SAT` composes to `NPhard'' SAT` — swap the headline over and delete the
   legacy `⪯p` front (that IS the S2 collapse).
4. **Off the critical path, fully independent** (the right pick for a parallel
   agent): the SAT-verifier Split adaptation for the in-NP half of
   `NPcomplete'' SAT` — see the C8 endgame note above.

**Do NOT** re-open `s1Key`, the `EScratch`/`CDirty` predicates, or either stage
contract from the top-down side: `yesBranch_run` is proven against all three.

**Reusable machinery — do not re-derive**: `Lang/CostFlat.lean`; the witness
templates (`flatTCC_reductionLang`, `binaryCCFSAT_reductionLang`,
`fsatSAT_reductionLang`, field for field); the three live seams; the
2026-07-16 cost-assembly pattern (per-branch `private` lemmas + precomputed
frame facts + `clear_value` discipline + symbolic `flatK` constants).

## NEXT BOTTOM-UP session — stage M-yes, then stage C family by family

⚠ **READ FIRST: the two stages are no longer free-form.** Their statements are
already fixed and *consumed* by `S1Program.yesBranch_run`:
`S1Program.stageC_run` and `S1Program.stageMYes_run`. **Fill in the `def` and
replace the `sorry` in the existing theorem — do not restate either lemma.** A
changed contract re-opens the whole yes branch. Likewise `stageC_usesBelow` /
`stageMYes_usesBelow` (`by simp [<every def>, Cmd.UsesBelow, Op.UsesBelow,
<every register def>]`, the `stagePG_usesBelow` pattern — `by decide` does not
work on `UsesBelow`). When both land, re-point `probes/S1ProgramProbe.lean` §2
at `s1Program` itself (see FINDING B).

1. **Stage M-yes (small — start here, half a day).** `EOUT_T := 1^(steps + 1)`
   then five copies into the output registers:
   ```
   copy EOUT_T 4 ;; appendOne EOUT_T ;;          -- BEFORE any output write
   copy 1 EOUT_S ;; copy 2 EOUT_I ;; copy 3 EOUT_C ;; copy 4 EOUT_F ;;
   copy 5 EOUT_T
   ```
   ⚠ **Order matters**: registers `1`–`4` are the *input* layout, so `EOUT_T`
   must be built from register `4` (`S1Emit.HSTP`, `1^steps`) *before*
   `copy 4 EOUT_F` overwrites it, and nothing may read registers `1`–`4`
   afterwards. The `+1` is `guessTableauTyped.steps = steps + 1` — do not
   "simplify" it to a copy (`probes/S1ProgramProbe.lean` §4 prints the
   difference).
   The contract's conclusion is `s1Extract (stageMYes.eval s) = s1Key
   (guessTableau …)`; the card component closes with **`S1Cards.encCards_eq`**
   (`encCardsIn (guessTableau …).cards = encNats (cardBlocks M)`), the other four
   are `rfl` against `FlatTCC.flattenTCC`'s fields. `EOUT_T` may be any register
   in `EScratch`; the contract does not name it.
2. **Stage C, family by family — the big one, now fully templated.** Target:
   `EOUT_C := FlatTCCFree.encNats (S1Cards.cardBlocks M)`, and `cardBlocks` is an
   explicit `++` of seven streams with a per-family equation already proven, so
   build and prove **one family per sitting**, in this order:
   a. `copyBlocks` (three plain loops, no gating) — the template: six value
      registers, `emitBlk` ×6 in the innermost body, each value register
      maintained incrementally exactly as `stageFin`'s `EC` is (FINDING 3).
   b. `copyRightBlocks` (two loops), then `haltLeft/Center/RightBlocks` (adds
      the `PHALT` **random-access** gate — a `forBnd` bounded by `1^q` walking
      `PHALT`; stage F's sequential drain does not apply here).
   c. `preludeBlocks`: materialise `resOf k` into a register per kind
      (value/class pairs) and scan it three times; the premise triple is
      `Sg M + kᵢ` (`S1Cards.pcellv`), the filter is `contigB` on three class
      codes.
   d. the transition families: first the dedup pass
      (`S1Cards.normModel`/`normModel_eq` — three-number keys in one "seen"
      register, `O(T²)` iterations of constant work), then `stepBlocks`'s four
      sub-nests off the nine parsed numbers.
   ⚠ Counts and scale: `Θ((1+Q+T)·σ³)` cards, `Θ(n⁵)` cells; numbers in
   `probes/S1CardModelProbe.lean` §3–4. Re-`#eval` that probe after any model
   change. **Measured (FINDING D): the card register is `>99.8%` of the whole
   emitted output** (`132051` cells vs `22 + 76 + 30 + 1` for Σ/I/F/M on the
   smallest probe instance) — stage C alone is the cost ladder.
   ⚠ **Register budget — now a stated contract, `S1Program.CDirty`**: stage C may
   dirty `EOUT_C`, all of `EScratch` (`[37,48)` + `HEAD`/`INBLK`/`SKIPR`) **and
   the whole P/G scratch block `[14,32)`** — including `FLG` (17), which nothing
   re-reads (FINDING E). It must NOT touch `1`–`5`, `PSIG` (6), `PSTATES` (8),
   `PHALT` (11), `PTRANS` (13, which it re-scans), `EOUT_S` (32) or `EOUT_I`
   (33). If it needs a register outside `CDirty`, widen `CDirty` and re-check
   `yesBranch_run` — it is the only consumer.
   ⚠ Each family's `_run` may assume the guard (`validFlatTM M`, `M.tapes = 1`)
   — `stageC_run` already takes both as hypotheses, supplied by
   `S1Map.s1GuardB_iff` at the call site.
3. **The cost ladder, LAST** — `S1Witness.s1_reductionLang.cost_le`, now the
   witness's ONLY open field. Measured cubic for P+G; `emitBlk_cost`
   (`≤ 3 + 5v + v²`) is the leaf and `Cmd.cost_forBnd_le` sits above each loop.
   Assemble once, after every stage exists, and remember: **raise `cost_bound`
   rather than fight for degree 10** (it only has to dominate the cost and
   `S1Map.s1Map_size_le`). Per FINDING D, budget the whole program as stage C's
   cost plus a constant-factor slack.

**Recommendation: run a BOTTOM-UP session next**, on item 1 (stage M-yes — half
a day, and it turns `yesBranch_run` into a one-`sorry` result) and then item
2a–2b (the copy and halt card families, which establish the stage-C emitter
template on the two simplest of the seven families). A parallel agent should
take the top-down seams (items 1–2 above): different files, no dependency on
stage C, and they are the last unvalidated *structural* interface left.

---

## Locked invariants — do NOT revisit

- **The S1 program's SHAPE and the two stage contracts are PINNED
  (2026-07-26-b, `Reductions/S1Program.lean`)**: `s1Program = stagePG ;; ifBit
  FLG yesBranch stageMNo`, `yesBranch = Σ ;; I ;; C ;; F ;; M-yes`, and
  `stageC_run` / `stageMYes_run` state exactly what the assembly consumes.
  `s1Program_computes` is already the witness's `computes` field. Changing the
  stage order, either contract, or the `EScratch`/`CDirty` licences re-opens
  `yesBranch_run` and hence `computes`.
- **`s1Key`/`s1Extract`/`SIGMA`…`STEPS`/`s1RegBound` live in `S1Program`, not
  `S1Witness` (2026-07-26-b).** The witness imports the program. Do not move
  them back or duplicate them.
- **A skeleton-phase lemma must quantify over the placeholder it does not depend
  on (2026-07-26-b).** A `sorry` inside a `def` puts `sorryAx` in the axiom list
  of *every* lemma whose statement mentions it, proof or no proof — which blinds
  `#print axioms`, the project's main soundness instrument. `noBranch_computes`
  takes `(yes : Cmd)` and is axiom-clean; `s1Program_computes_neg` is its
  corollary and is not. State the general form first, specialise second.
- **The emitter register frame is PINNED (2026-07-26, `Reductions/S1Emit.lean`)**:
  `32`–`36` are the five stage outputs (Σ, I, C, F, `1^(steps+1)`) and persist
  to stage M; `37`–`47` are shared scratch every stage reuses. Changing it
  re-opens `stageSig_run`, `stageFin_run`, `stageInit_run` and all three
  `usesBelow`s.
- **Every size bound over an encoding with a fixed-size header needs an ADDITIVE
  term (2026-07-26).** `size (flattenTM M) ≤ 3·size M` was stated as having
  "slack" and is false at the trivial machine (`size M = 1`, six header cells).
  The correct shape is `c·size M + d`; `d = 3` here and is tight. Probe the
  empty/zero instance of every new size claim — a probe over "realistic"
  instances will print `true` and hide it (`probes/S1SizeGapProbe.lean` §3).
- **Stage C's target is `S1Cards.cardBlocks` (2026-07-25-c)** — the seven
  `List.range` streams, in that order, `emb`-free. Changing the model re-opens
  ten proven equations; extend it only by adding a family at the end (and
  re-run `probes/S1CardModelProbe.lean`).
- **The output register is built by unit-cost APPENDS, never `concat`
  (2026-07-25-c).** `Op.cost (concat dst a b) = 2(|a|+|b|)+1` reads the whole
  destination, so one `concat`-per-card would be quadratic in the emitter's own
  output. Same rule for every future large-output emitter.
- **`cost_bound` is a free polynomial, but it also carries `output_size_le`
  (2026-07-25-c).** `PolyTimeComputableLang.output_size_le` is stated against
  `cost_bound`, so any raise must keep dominating `S1Map.s1Map_size_le`; that
  is the only constraint. Never re-engineer a program to meet a self-imposed
  degree.
- **The S1 program's register frame is PINNED (2026-07-25-b,
  `Reductions/S1Parse.lean`)**: `0` `ZERO` (ends `[]`), `1`–`5` the head
  layout / output registers, `6`–`13` stage P's persistent outputs, `14`–`31`
  P/G scratch, `32`–`47` free for stages Σ / I / C / F / M, `s1RegBound = 48`.
  Registers **`15`, `16`, `22`, `26` are RESERVED** — `CliqueRelTM.readNum` /
  `ltBit` hard-wire them. Changing any of this re-opens `stagePG_usesBelow`,
  `stagePG_frame` and every stage built on top.

- **`encodable FlatTM` is the DATA-FIELD SUM (2026-07-25):**
  `sig + tapes + states + start + size halt + size trans + 1`, next to the
  instance in `Definitions.lean`. The old `sizeFlatTM` (flat `5` per
  transition entry) is deleted; never reintroduce a "roughly / approximate"
  size measure. This is what makes the S1 witness's `encodeIn_size`
  satisfiable at all (`probes/S1SizeGapProbe.lean`).
- **The S1 witness's OUTPUT layout is `FlatTCCFree.encodeIn` verbatim on
  registers 1–5 (2026-07-25, `S1Program.s1Key`)** — the sound-tail composite's
  `encodeIn` *is* `FlatTCCFree.encodeIn` (`rfl`), which is what makes the
  fourth seam a pure scrub of reg `0` and `[6, 57)`. Changing `s1Key` now
  re-opens the seam **and** `yesBranch_run`/`computes`.
- **The flat tape is APPEND-ONLY AT THE FRONTIER (2026-07-17-b):**
  `writeCurrentTapeSymbol` replaces in range, appends exactly at
  `head = right.length`, and is a NO-OP strictly beyond. Never reintroduce
  the zero-padding jump-write — it is non-local (one step rewriting cells
  arbitrarily far from the head) and falsifies every local-window tableau
  simulation (S1). New machines must not rely on writing past the frontier.
- **S1 rows carry a RIGHT boundary marker (2026-07-18-c)** — `confRow` ends
  with `bCell`, guarded by the cell-preserving `copyRightCards` family, and
  the step lemmas demand `cfgHead + 4 ≤ n` head-room. Never drop the
  marker, add another family with the marker in slot 3, or add ANY
  head-at-second-slot family: each reopens the machine-checked phantom-head
  completeness hole (`probes/S1TableauProbe.lean` §5).
- **`BitState` / `sig = 4` / numbers UNARY (Option B′).** Fixed 4-symbol
  alphabet; `encodeTape` shifts cells `+1` (`0→1`,`1→2`), `0` separates
  registers, `3` terminates/anchors. Every tape-touching state must be
  `Compile.BitState` (cells `∈ {0,1}`). Numbers unary (`enc n = replicate n 1`).
- **Runtime tape-padding resolves the register-count WALL.** `Compile.padRegsTM
  k` grows the tape during the run; `paddedBitDecider_run`/`paddedCompute_run`
  are proven with **no `k ≤ s.length`**.
- **`physStepBudget G cost = (9G²+9G+33)·(8·cost+8) + cost`** is the only
  composable budget shape. Never an `overhead`/`(·+1)²` shape.
- **`DecidesBy.encode_size` is per-decider POLYNOMIAL** (`encodeBound`).
- **Per-op contract takes a threaded scratch base `sb`**; eqBit-style ops use
  pre-existing interior scratch at `sb`/`sb+1`.
- **`Op.cost eqBit = |src1|+|src2|+1`**, **`Op.cost concat =
  2(|src1|+|src2|)+1`** (size-aware costs).
- **`NPhard'` endpoint-only; chains compose via `SeamData`/`comp`** (settled
  2026-07-02, VALIDATED LIVE 2026-07-03). No generic `⪯p'`-transitivity — do
  not attempt one.
- **No size-0 `encodable` fallback** (Part 0.1, 2026-07-04-b): the default
  instance is deleted; a missing `encodable.size` is a compile error by
  design. Give every new type a real data-field-sum size next to its
  definition.

## Proven, reusable — do not re-derive

- **The S1 program assembly (2026-07-26-b, `Reductions/S1Program.lean` — consume
  as black boxes; do NOT re-assemble the program or restate a stage contract)**:
  the output-key layout `s1Key`/`s1Extract`/`SIGMA`…`STEPS`/`s1RegBound` (moved
  here from `S1Witness`); the coarse frame predicates **`EScratch`**/**`CDirty`**
  + `ne_of_not_scratch`/`ne_of_not_cdirty` and the three corollaries
  **`stageSig_frame`/`stageInit_frame`/`stageFin_frame`** (`¬ EScratch r →
  r ≠ <own output> → get (stage.eval s) r = get s r` — the shape every new stage
  should be stated in); the suffix defs `ySuf1`/`ySuf2`/`ySuf3` and **`yesBranch`
  / `s1Program`**; `s1Key_s1No`; **`noBranch_computes`** (axiom-clean, over an
  arbitrary yes branch) → `s1Program_computes_neg`; **`yesBranch_run`** and
  **`s1Program_computes_pos`**; **`s1Program_computes`** (the witness field) and
  **`s1Program_usesBelow`**. OPEN in this file: `stageC`/`stageC_run`/
  `stageC_usesBelow` and `stageMYes`/`stageMYes_run`/`stageMYes_usesBelow`.
  Probe: `probes/S1ProgramProbe.lean`.
- **The S1 emitter atom + stages Σ / I / F (2026-07-26, `Reductions/S1Emit.lean`,
  sorry-free & axiom-clean — consume as black boxes; do NOT re-derive an
  append gadget or restate the prelude row / final patterns)**: the atom
  **`emitBlk`** + `emitBlk_run` / `emitBlk_cost` (`≤ 3 + 5v + v²`) /
  `emitBlk_usesBelow` (register-generic); `loadSg` / **`loadSg_run`**
  (`1^(Sg M)`, the only multiplication, hoisted); **`stageSig`/`stageSig_run`/
  `stageSig_usesBelow`**; the stage-F model `finBlocks` + **`finBlocks_eq`** and
  **`stageFin`/`stageFin_run`/`stageFin_usesBelow`**; the stage-I models
  `cellsA`/`cellsB`/`cellsC`/`initBlocks` + **`initBlocks_eq`** (guarded) and
  **`stageInit`/`stageInit_run`/`stageInit_usesBelow`**; the shared loop
  machinery `repOne`/`repOne_run`, `iniCellK`/**`iniLoopK_run`** (a
  constant-value cell loop with a first-iteration bonus — reuse it for any
  "same value every iteration except the first" stream), `enop`; and the codec
  algebra `encNats_singleton`, `encFinal_append`, `encFinal_singleton`, plus the
  list helpers `drop_getElem_cons`/`tail_drop_succ`/`getD_of_le`/
  `encSyms_len_ge`. Probe: `probes/S1EmitProbe.lean`.
- **The `encodable.size` list algebra (2026-07-26, `Reductions/S1Witness.lean`,
  project-wide utility)**: `nat_size_append`, **`list_size_map_sum`**
  (`size l = (l.map (size · + 1)).sum` — the lemma every list size argument
  wants), `list_size_cons`, `nat_size_flatMap`, `length_eq_sum_ones`,
  `mul_sum_map`; the per-field bounds `opts_size_le`/`moves_size_le`/
  `halt_size_le` (each in the "payload + its own item slot ≤ 2·charge" shape)
  and `entry_size_le`; and **`flattenTM_size_le`** (`≤ 3·size M + 3`).
- **The stage-C pure model (2026-07-25-c, `Reductions/S1Cards.lean`,
  sorry-free & axiom-clean — consume as black boxes; do NOT restate the card
  stream from `guessCards`)**: the plumbing `cnats`/`cardsFlat` +
  `cardsFlat_append`/`_flatMap`/`_map`/`_filterMap`, `encNats_append`,
  `encCardsIn_eq_encNats`; the change-of-variables trio `flatMap_finRange` /
  **`finRange_flatMap_congr`** / **`map_finRange_congr`** (turn any
  `finRange` nest that only uses `.val` into a `List.range` nest — reusable
  project-wide) and **`xOpts_flatMap`** (the `xOpts` enumeration as
  `range (σ+2)`, index `0` = boundary marker, blank-flag ⇔ index `= σ+1`);
  the cell arithmetic `bv`/`sgv`/`hv`/`xv`/`blk` + `bv_eq`/`sgv_eq`/`hv_eq`/
  `tv_eq`/`xv_zero`/`xv_succ`/`xIsBlank_eq`/`xIsBlank_none`; `haltBit` +
  **`haltBit_eq`** (the raw `PHALT` bit list decides `M.halt.getD` at every
  index, in range or not); the option codec `oTag`/`oVal`/`oTag_oVal_inj`,
  `rOf`/`wOf` + **`rOf_eq`/`wOf_eq`** (`optSym`/`wEff` as arithmetic on the
  `(tag,val)` pairs); the seven family models `copyBlocks`/`copyRightBlocks`/
  `haltLeft|Center|RightBlocks`/`stepBlocks` (`stepCenter|Left|Right|InBlocks`)/
  `preludeBlocks` (`pBody`/`resOf`/`contigB`/`kindIdx`/`pcellv`/
  `pKindList_flatMap`/`resOf_eq`/`contigB_eq`) with **one equation per family**
  (`copyCards_flat`, `copyRightCards_flat`, `haltLeftCards_flat`,
  `haltCenterCards_flat`, `haltRightCards_flat`, **`stepCardsOf_flat`**
  (hypothesis-free — `headD` makes it hold for malformed entries too),
  `stepCards_flat`, `preludeCardsOf_flat`, `preludeCards_flat`,
  `cookCards_flat`); the endpoints **`cardBlocks_eq`** and **`encCards_eq`**;
  the `normTrans` spec `keyOf`/`sameKey_eq`/`entryOK_eq`/`dedupK`/
  `dedupK_subset`/`dedupGo_eq_dedupK`/`normModel`/**`normModel_eq`**; and
  stage M's no-branch `stageMNo` + `stageMNo_run`/`_frame`/`_usesBelow`.
  Probe: `probes/S1CardModelProbe.lean`. (⚠ this un-`private`d
  `CookTableau.dedupGo` — visibility only.)

- **The S1 program stages P + G (2026-07-25-b, `Reductions/S1Parse.lean`, all
  axiom-clean, sorry-free — consume as black boxes; do NOT re-derive the parse
  or the guard)**: the pinned register frame (`ZERO`…`I5`, see "Latest
  session"); the pure stream model `optsFlat`/`transFlat` + `optsFlat_eq`/
  `transFlat_eq`/`flattenEntry_eq`/`flattenEntry_append`/`flattenTM_eq`/
  `flattenTM_cons` (the `foldl`→`flatMap` bridge, via the private
  `foldl_append_nil`); the item algebra `itemOf`/`encSyms_nil`/`encSyms_cons`/
  `encSyms_cons'`; **`readItem`/`readItem_run`** (one `encSyms` item off a
  cursor, `RegOK` bundling `readNum_run`'s twelve side conditions);
  `bitOf`/`haltBody`/**`haltLoop_run`**; **`stageP`/`stageP_run`** (all eight
  parsed registers); the flag gadgets `nop`/`andIn`/`ltCheck`/`eqCheck` +
  `andIn_run`/`ltCheck_run`/`eqCheck_run`; the scan invariants
  `EInv`/`EInv_set`/`EInv_frame` + the step lemmas `readVal_step`/
  `ltStates_step`/`ltSig_step`/`eqTapes_step`; **`optCheck`/`optCheck_run`**
  (the variable-arity `Option Nat` core), `optLoop_run`/`skipLoop_run`,
  `fieldCheck`/`arityOptCheck`/`arityMoveCheck` + `_run`, **`entryBody_run`**,
  **`entryLoop_run`**; `SInv`/`sBody`/**`sLoop_run`** (the idle-tolerant input
  scan); the `Bool` bridge `entryPB`/`entryPB_eq`/`isValidFlatTM_eq`/
  **`s1GuardB_eq`**; **`stageG`/`stageG_run`**, **`stagePG`/`stagePG_run`**,
  **`stagePG_usesBelow`** (`32`) and **`stagePG_frame`** (registers `1`–`5`
  untouched). Probe: `probes/S1ParseProbe.lean`.

- **The S1 reduction map (2026-07-25, `Reductions/S1Map.lean`, all axiom-clean
  — consume as black boxes; do NOT re-derive the guard or the correctness
  iff)**: `optAll_iff`/`entryB_iff` → **`isValidFlatTM_iff`** (`Bool` ↔
  `validFlatTM`); `s1GuardB` + **`s1GuardB_iff`** (the three decidable
  instance-validity conjuncts = exactly `guessTableau_correct`'s hypotheses);
  `s1No` + `s1No_not_lang` (the off-guard image: `init = []` fails
  `FlatTCC_wellformed`); `s1Map` with the branch equations
  **`s1Map_pos`/`s1Map_neg`** (⚠ the `match` does NOT reduce under `unfold` —
  always go through these); **`s1Map_correct`**; `s1_param_le` (every tableau
  size parameter ≤ the instance's `encodable.size`); `s1Bound`/`_poly`/`_mono`
  and **`s1Map_size_le`** (`≤ (2·(n+3))^10`, the `output_size_le` field).
- **The S1 witness (2026-07-25/-26/-26-b, `Reductions/S1Witness.lean`)**:
  `encNats_append`, `encCardsIn_eq`, `cardNats_injective`,
  `flatMap_cardNats_injective`, **`encCardsIn_injective`**,
  **`s1Key_injective`** (⇒ `decodeOut = Function.invFun s1Key` is honest);
  `encSyms_length` (`= sum + 2·length`), `list_nat_size_eq`
  (`encodable.size l = sum + length`), **`encSyms_length_le_size`**
  (`≤ 2·encodable.size l` — the generic head-layout size step);
  **`flattenTM_size_le`** (`≤ 3·size M + 3`) and `headEncodeIn_size_le`
  (`≤ 8·n + 4`); and the witness **`s1_reductionLang`** with `computes`
  (= `S1Program.s1Program_computes`), `usesBelow`, `decode_agree` and every
  mechanical field discharged. **OPEN in this file: `cost_le` only.**
  (`s1Key`/`s1Extract`/`SIGMA`…`STEPS`/`s1RegBound` moved to `S1Program`.)
- **The C8-3 front-piece layer (2026-07-18-b,
  `Reductions/FrontPieces.lean`, all axiom-clean, register-generic —
  C8-4/C8-5 consume these verbatim)**: `appendConst_run` (seed-`Cmd`-glued
  constant append, exact cost `+2/cell`), `emitConst_run`/`_bits`,
  `appendItem_run` (the `encSyms` item), `reencBody`/`reencLoop_run`
  (bit register → `encSyms ((·+off)`-shifted stream), `scan` drained, `src`
  intact, quadratic cost), `mulStep_run`/`powLoop_run` (`acc := 1^(a·m^k)`
  on `unaryMulLoop_run`, cost `powCost` + closed form `powCost_le`),
  `unaryMonomial_run` (`dst := 1^(c·(n+1)^k+d)`, cost `monomialCost`);
  `HeadLayout.encSyms_snoc` (the `encSyms` loop-invariant closer). **Added
  2026-07-19-c**: `emitRegs`/`emitRegs_run` (the reg-2 input-string emitter —
  `dst := encSyms (3 :: encodeRegs (srcs.map get))`, `src` regs intact, only
  `dst`/`scan`/`tflg`/`cnt` touched) + **`emitRegs_cost`** (2026-07-24-b:
  `≤ 11 + Σ_{src} emitRegCost |src|`, `emitRegCost L = 8+13L+2L²`; mirrors
  `tallyCells_cost`'s `foldl` induction) and `HeadLayout.encSyms_append` (encSyms
  distributes over `++` — the closer for every `encSyms`-of-a-concatenation goal).
  **The whole-program cost `FrontProgram.frontProgram_cost_le`** (2026-07-24-b)
  bounds `(frontProgram …).cost` by `emitRegs.cost + 2·monomialCost + emitConst +
  the five copy costs` (copy sources read off the emitted registers), mirroring
  `frontProgram_run`'s s1…s4 threading. **Added 2026-07-19-d**:
  `tallyReg`/`tallyReg_run` (single register: `dst := dst ++ 1^|src|`,
  `forBnd`-bounded-by-`src` appending one `1`/cell, cost `≤ 1+|src|·5+|src|²`
  via `cost_constLoop_le`) and `tallyCells`/`tallyCells_run`/`tallyCells_cost`
  (the R2 input-cell counter: `dst := 1^(Σ_{src ∈ srcs}|get src|)`, sources
  read-only, only `dst`/`cnt` touched; for `srcs = List.range xWidth` the count
  is `State.size (encX x)` — the `unaryMonomial` argument `n`; cost
  `≤ 1 + Σ(2+|src|·5+|src|²)`, the foldl-cost template `emitRegs`'s missing cost
  bound should copy). All `[propext, Quot.sound]`; probe `C8FrontProbe` §6.
- **The C8-4 front machine + machine-iff (2026-07-20,
  `Reductions/FrontMachine.lean`, all axiom-clean — consume as black boxes for
  the C8-4 witness's correctness field)**: `MQ c k w` (the accept-by-halting
  front machine over an abstract verifier `Cmd`), `rejectState`/`acceptState`
  (`+2`/`+1` shifted, `acceptState_ne_rejectState`), `M2` (the demoted decider);
  the structural lemmas `MQ_sig`(= 4)/`MQ_tapes`(= 1)/`MQ_states`/`MQ_valid` +
  `paddedBitDeciderTM_sig`/`M2_sig`/`_tapes`/`_valid` +
  `paddedBitDeciderTM_halt_rejectState`; the **explicit budget** `MQbudget c k s`
  (the F6 overshoot target); **forward** `MQ_accepts_of_accept` (verifier
  accepts `sx++[creg]` ⇒ `M_Q` accepts `(3::encodeRegs sx)++(shiftReg creg++[0,3])`
  for `steps ≥ MQbudget`) and **backward** `MQ_no_reject_of_accepts` (`M_Q`
  accepts `(3::encodeRegs sx)++cert` ⇒ `cert = shiftReg creg++[0,3]` bit-valid ∧
  `(c.eval (sx++[creg])).get 0 ≠ [0]`; frame hyp is the single `w+1 ≤ k`).
  Probe `probes/C8MachineProbe.lean` (`#eval acceptsFlatTM M_Q` on yes/no/garbage
  certs). Do NOT re-derive the compose/demote/format-check plumbing.
- **The C8-4 abstract lifting (2026-07-20-b, `Reductions/FrontLifting.lean`, all
  axiom-clean — consume as black boxes for the C8-4 witness's correctness field;
  do NOT re-derive the predicate-level lift)**: `fQ W maxSize steps` (the per-`Q`
  front instance, `maxSize`/`steps` abstract), **`fQ_correct`** (the iff,
  parameterized over `maxSize`/`steps` with the two domination hyps `hmax`
  (`certBoundOf + 2 ≤ maxSize`) / `hsteps` (`MQbudget ≤ steps` on size-bounded
  certs)), and **`fQ_correct_concrete`** (hypothesis-free, with concrete
  `maxSizeOf`/`stepsOf`). Supporting: the codec `certReg`/`decodeReg` +
  `certReg_decodeReg` + `certState_eq`; `list_length_le_size`; `encX_bit`/
  `xWidth_succ_le`; `certBoundOf`/`cert_complete`/`cert_sound` (classical cert
  bound from `rel_correct`); `argBound`/`dCap`/`front_state_bounds` (the split
  pair `encX x ++ [certReg c] = verifier.encodeIn (x,c)`, so `State.size`/cost/
  width route through the verifier's own bounds); `MQbudget_le`; the `inOPoly`
  proofs `certBoundOf_poly`/`argBound_poly`/`dCap_poly`/`maxSizeOf_poly`/
  `stepsOf_poly` (helper `lin_dCap_poly`).
- **The C8-4 reduction program (2026-07-20-c, `Reductions/FrontProgram.lean`,
  `[propext, Quot.sound]` — consume as a black box for the C8-4 witness's
  `computes`/`cost` fields; do NOT re-derive the wiring)**: `frontProgram
  MQconst xWidth B cm km dm cs ks ds` (the four-register emitter: `emitRegs`
  into scratch `B`, two `unaryMonomial`s into `B+1`/`B+2`, `emitConst` into
  `B+3`, then `clear 0` + 4 copies into output regs 0–4) and
  **`frontProgram_run`** (regs 0–4 = `headEncodeIn (M_Q, 3::encodeRegs(input),
  cm·(m+1)^km+dm, cs·(m+1)^ks+ds)` for input split as `encX x ++ [1^m]`,
  hyps `5 ≤ B`, `xWidth < B`, `MQconst` bit-level, size reg `= 1^m`, sources
  bit-level). Probe `probes/C8ProgramProbe.lean`. ⚠ **no cost lemma yet** —
  the next bottom-up session adds `emitRegs_cost` + `frontProgram`'s cost bound
  (the `UsesBelow` lemmas were added 2026-07-24 — see below).
- **The C8-4 witness `WQ` + endpoint reduction (2026-07-24,
  `Reductions/FrontWitness.lean`, all axiom-clean EXCEPT the two cost sorries
  `cQ_cost_le`/`fQ_output_size_le`; consume these verbatim in C8-5 and to close
  the cost ladder)**: **`front_reducesPolyMO' : Q ⪯p' FlatSingleTMGenNP`** (the
  endpoint) and `WQ` (the `PolyTimeComputableLang (fQ …)` witness);
  `encSyms_injective` + `decodeSyms`/`decodeSyms_encSyms` (genuine left inverse,
  no `Classical`); **`inOPoly_monomial_bound`** (F6 constant extractor,
  reusable anywhere); the gadget `UsesBelow` family
  `appendBit`/`appendConst`/`emitConst`/`appendItem`/`reencBody`/`reencLoop`/
  `emitRegs`/`mulStep`/`powLoop`/`unaryMonomial`/`frontProgram`_`usesBelow`;
  the list/state helpers `get_append_lt`/`get_append_last`/`map_range_get`/
  `size_append_one`/`get_mem`/`encSyms_cons`; and the witness scaffolding
  `encodeInQ`/`decodeOutQ`/`MmachineQ`/`MconstQ`/`BwidthQ`/`MmaxF`/`MstepF`/`cQ`
  + `computesQ`/`encodeInQ_size_le`/`_width`/`_bit`/`_bits`/`decodeOutQ_agree`/
  `BwidthQ_ge5`/`xWidth_lt_BwidthQ`. Do NOT re-derive the `computes`/lift wiring.
- **The S1 cell-code algebra (2026-07-18-b, `Simulators/CookTableau.lean`)**:
  `hCell_val_lb`/`hCell_val_ub`, `tCell_ne_hCell`/`hCell_ne_bCell`/
  `tCell_ne_bCell`, `hCell_inj`/`tCell_inj` — the three disjoint code bands;
  built for `halt_of_satFinal` (now proven), reused by the (1b) inversion's
  card-classification stage.
- **The S1 (1a) layer (2026-07-18, `Simulators/CookTableau.lean`, all
  axiom-clean)**: `stepFlatTM_normM` + `normTrans_subset`/`dedupGo_subset` +
  the `dedupGo` `find?` lemma family; `step_desc` (unfolded step: fired
  entry + payload + successor shape) and `write_facts` (the packaged write
  effect incl. the `wEff`-at-frontier-flag head-cell fact) — consume these
  for EVERY remaining S1 direction; `ConfFits_init`/`ConfFits_step`; the
  window machinery (`rowCell`/`rowX`/`confRow_window`/`take3_drop`/
  `coversHead_take3`, frontier detection `tapeSymAt_blank_iff`/
  `rowX_isBlank`, membership lemmas for all five step families + all four
  copy/halt families, `copy_window`); `validStep_of_step`/
  `validStep_of_halt`/`satFinal_of_halt`. **The S1 trajectory + right-marker
  layer (2026-07-18-c)**: `ConfFits_mono`, `isValidFlatTapes_single`,
  `relpower_of_run`/`cover_of_run`, `run_of_relpower`/`run_of_cover`, and
  the marker machinery `copyRightCards` + `copyRightCard_mem(_cookCards)`,
  `confRow_getElem_last`/`confRow_window_last`/`copyRight_window`.
  **The S1 (1b) inversion layer (2026-07-18-d — all axiom-clean; the whole
  bijection `cookTableau_correct` now sorry-free)**: `window_card`
  (covering ⟹ six cell equations) on the total coordinate view
  `rowCellM`/`confRow_getElem'`; `cookCards_cases`/`stepCardsOf_cases`
  (membership by family); the shape lemmas `card_headfree_middle`/
  `card_bfirst`/`card_blast`/`card_head_center`; key uniqueness
  `dedupGo_notin_seen`/`dedupGo_pairwise`/`normTrans_find?_eq`;
  `stateOf_inj_lt`/`optSym_inj_valid`/`xCell_inj`/`xCell_ne_hCell`; the
  pinning lemmas `validStep_zero`/`validStep_last`/`validStep_away` and
  the `assemble_row` scaffold — if the prelude layer special-cases row 0,
  ALL of this is reused unchanged on rows 1…steps. **The frozen head layout**
  (`Reductions/HeadLayout.lean`): `headEncodeIn`/`headRegBound`/`encSyms`/
  `flattenTM` + `headEncodeIn_bitState` — the S1 witness's `encodeIn` and
  C8-5's seam target; imported by `Complexity.lean`, consumed by
  `probes/C8SeamProbe.lean`.
- **The S1 prelude/guess layer (2026-07-19/-b, `Simulators/GuessTableau.lean`;
  everything PROVEN & axiom-clean — `guessTableau_correct` is sorry-free)**:
  the band alphabet `PSg`/`emb`/`embCard` + `emb_inj`/`emb_val_lt`/`pCell_ge`/
  `preludeCard_shape`/`preludeCard_prem_ge`; the construction
  `PKind`/`pCell`/`pResolutions`/`contigOK`/`preludeCardsOf`/`preludeCards`/
  `guessCards`/`pKindAt`/`preludeRow`/`guessWidth`/`guessFinal`/
  `guessTableau(Typed)` + `guessTableau_wellformed`; the Γ-transfer layer
  `isPrefix_map_emb`/`prelude_no_cover_emb`/`coversHead_emb_of`/`_inv`/
  **`validStep_emb` (T1)**/`exists_preimage_map_emb`/`validStep_emb_row`/
  **`relpower_emb` (T2 — ⚠ requires `3 ≤ a.length`)**/`relpower_emb_of`/
  **`satFinal_emb` (T3)**; **the shared coordinate spine** `gKind`/`gCls`/
  `preludeRow_getElem?`/`gRes_mem`/`confRow_res_mem`/`gCls_cut_live`/
  `gCls_contig` + the membership algebra `pCell_inj`/`pKindList_mem`/
  `preludeCardsOf_mem`/`preludeCards_mem`/`pRes_*_mem`; **P1**
  `prelude_validStep_of_cert`; **the P2 inversion** `cert_of_prelude_validStep`
  with `decodeSym`(`_tCell`/`_hCell`)/`starRes_class`/`star_res_cases`/
  `initStar_res_cases`/`prelude_window_shape`. The eventual S1 witness's guard
  is exactly `guessTableau_correct`'s hypotheses; consume `guessTableau_correct`
  as a black box. Probe: `probes/S1TableauProbe.lean` §6. (⚠ this un-`private`d
  the `CookTableau.lean` window lemmas `rowCell`/`confRow_getElem[_last]`/
  `confRow_window[_last]`/`take3_drop`/`coversHead_take3` — visibility only.)
- **The S1 size-bound layer (2026-07-24-c, all axiom-clean — the generic
  toolkit is a project-wide `encodable.size` utility, consume everywhere)**:
  in `CookTableau.lean` — generic `encodable_size_list_le` (`size l ≤ (c+1)·|l|`),
  `length_flatMap_le` (`(l.flatMap f).length ≤ |l|·c`, pass `c` EXPLICITLY),
  `flattenString_size_le` (`≤ (k+1)·|xs|`), `flattenCard_size_le` (`≤ 6k+1`),
  `pow_collapse` (`total ≤ C·b^d`, `C≤1024`, `d≤10` ⇒ `≤ (2b)^10`); the M-only
  card counts `xOpts_length`, `copyCards`/`copyRightCards`/`haltLeftCards`/
  `haltCenterCards`/`haltRightCards`/`stepCardsLeft`/`stepCardsOf`/`stepCards`_
  `length_le`, `dedupGo_length_le`→`normTrans_length_le`, `cookCards_length_le`
  (`≤12·(σ+states+|trans|+3)^4`), `cookFinal_length_le`/`_mem_length`; and
  **`cookTableau_size_bound`** (`≤ (2·(n+1))^10`). In `GuessTableau.lean` —
  `pResolutions_length_le`/`pKindList_length`/`preludeCardsOf_length_le`/
  `preludeCards_length_le` (`≤ (5+2σ)³·(σ+1)³`), `guessFinal_length_le`/
  `_mem_length`, `PSg M ≤ 2b²`, and **`guessTableau_size_bound`**
  (`≤ (2·(gn+1))^10`, `gn` includes `maxSize`). Numerically validated:
  `probes/SizeBoundProbe.lean`.
- **The C8-2 gadget layer (2026-07-05)**: `AcceptHalt.demoteHalt` +
  structure/step/halting lemmas, `demoteHalt_run_eq`/`_weak`, the transport
  pair `demoteHalt_run_accept`/`_run_reject`, `acceptsFlatTM`-level
  `demoteHalt_accepts`/`_not_accepts`, and `runFlatTM_first_halt`
  (trajectory recovery from bare `run ∧ halting` — reusable wherever a
  consumer lacks a no-early-halt conjunct). `FormatCheck.formatCheckTM` +
  `formatCheck_run`/`_traj`/`_stuck`, `certOKB`/`certOKB_iff`/
  `encodeTape_certSplit`, and the **`Seg` framework** (exact run +
  done-state-free trajectory, additive composition — the template for any
  bespoke single-halt-state scan machine). `composeFlatTM_stuck_M1`
  (TMPrimitives): guard-stuck ⇒ composite-never-halts.
- **The FlatCC→BinaryCC free-reduction stack**
  (`Reductions/FlatCC_to_BinaryCC_free.lean`): `binConvert_run` (6-output run
  lemma with guard), the item view (`encItems`/`expandItems`/`itemsOkB` +
  `sitemsOf`/`citemsOf`/`fitemsOf` conversions), `sentLoop_run` (generic
  sentinel-stream transform loop), `initLoop_run` (bare-block loop),
  `mulLoop_run` (unary product), `remCheck_run` (truncated-subtraction
  compare + flag), `validB_iff` (Bool ↔ `isValidFlattening`),
  `encKeyB_injective`, `bitsNat_encodeString`/`cardsNat_encodeCards`/
  `finalNat_encodeFinal` (flat-level ↔ `Fin`-level correspondence),
  `encCardsOut_length_le`.
- **The live seams**: (`Reductions/FlatTCC_to_BinaryCC_comp.lean`) `scrub` +
  `scrub_eval`/`scrub_cost`, `flatTCC_to_binaryCC_seam`, the composed witness
  + `flatTCC_to_binaryCC_reducesPolyMO'`; (`Reductions/BinaryCC_to_FSAT_comp.lean`,
  2026-07-12) `scrub2`, `binConvert_key` (the predecessor's exit key as one
  local lemma), `get_nil_of_len_le`, `binaryCC_to_FSAT_seam` (seam ON a
  composed witness + the wider-right-frame length close),
  `flatTCC_to_FSAT_witness` + `flatTCC_to_FSAT_reducesPolyMO'`.
- **The `FSAT_to_SAT` run-lemma LEAVES** (`Reductions/FSAT_to_SAT_free.lean`,
  2026-07-13, all axiom-clean): `encodeCnf_append`/`_cons` (foldr-over-`++`
  distribution — the incremental-emission backbone); the emit-gadget
  projections `emitLit_{cnfout,frame,run}`, `endClause_run`, and per gadget
  `emit{TrueG,EquivG,AndG,OrG,NotG}_{cnfout,tally,frame}` (write exactly
  `encodeCnf (tseytin…)` onto `CNFOUT` + `numClauses` ones onto `TALLY`;
  frames via `Cmd.eval_get_of_not_writes`); the two sentinel-drain inner loops
  `drainSkip_run` (subtreeScan fvar-payload skip) / `drainVar_run` (tokenBody
  fvar read into `VREG`) + their per-shape `_done`/`_one`/`_zero` step helpers;
  and the **complete `budgetBody` dispatch** `budgetBody_frame`,
  `budgetBody_enter`, `budgetBody_{ftrue,fand,forr,fneg,fvar}` (⇒ pure
  `budgetStep_*`), `budgetBody_freeze` (bud=0). `budgetBody` is now factored as
  `nonEmpty NEB BUD ;; ifBit NEB budgetBodyInner nop`.
- **The `FSAT_to_SAT` run-lemma LOOP ASSEMBLIES** (same file, 2026-07-15, all
  axiom-clean — the machine ⇒ map obligation, DONE): **`subtreeScan_run`**
  (Dyck-forest `∃ gs` invariant folding the `budgetBody_*` leaves;
  `T = 1^(formula_size g)`), **`tokenBody_run`** (one iteration = one
  `scanClauses` token, per-shape dispatch integrating `subtreeScan_run`/
  `drainVar_run`/`emit*G`; frame via `tokenBody.writes`) with model bridge
  `tokHead`/`tokRem`/`scanClauses_tok`, **`outerLoop_run`** (Dyck-forest token
  loop; helpers `tokForest`/`tokForest_flatten`/`tokForest_sum`), **`Bloop_run`**
  (the `B := 1^|serF|` length loop), and **`buildSAT_run`** (the assembly:
  `(buildSAT.eval [serF f]).get CNFOUT = encodeCnf (fsatToSat f)` ∧
  `.get TALLY = 1^|fsatToSat f|`). The next witness's `computes` field is
  `buildSAT_run` + `decodeOut = invFun encodeCnf`. Do NOT re-derive.
- **The `FSAT_to_SAT` MECHANICAL FIELDS + LEAF COSTS** (same file, 2026-07-15-b,
  all axiom-clean): the 6 witness fields as standalone theorems — `serF_bit`/
  `encodeIn_bitState` (`enc_bit`), `encodeIn_size_le` (`encBound = 4n`),
  `encodeIn_width` (`width_le`), `buildSAT_usesBelow` (`FRAME = 27`),
  `buildSAT_computes` (`buildSAT_run.1` + `KSat3Free.encodeCnf_injective`),
  `fsatToSat_size_le` (`≤ 300·(n+1)²`, `output_size_le` fodder),
  `buildSAT_decode_agree`; and the 3 leaf loop-cost lemmas `drainVar_cost`/
  `drainSkip_cost` (via `Cmd.cost_forBnd_flat_le` + the `_SCAN_le`/`_SC2_le`
  scan-monotonicity helpers) and `Bloop_cost` (via `cost_constLoop_le`). The
  cost-assembly ladder consumes these unchanged. Do NOT re-derive.
- **The `FSAT_to_SAT` COST ASSEMBLY + WITNESS + SEAM** (2026-07-16, all
  axiom-clean): `tokenBody_cost` (`≤ tokFK·(E+N+3)³`; per-branch `private`
  lemmas `brTrue/brBin/brVar/brTag11/tree_cost`, `X_facts`/`sq_le_X`
  arithmetic helpers, precomputed `subtreeScan_fr_*`/`drainVarLoop_fr_*`
  frame one-liners, `drainVar_cost_le`); `outerLoop_cost` (semantic-invariant
  reuse + `tokRem_length_le`); `satOmega`/`satK`/`satBound` +
  `satBound_poly/_mono/_output`; `buildSAT_cost_le`; the witness
  `fsatSAT_reductionLang` + `fsatSAT_reducesPolyMO' : FSAT ⪯p' SAT`
  (`Reductions/FSAT_to_SAT_free.lean`); and the third seam `scrub3` +
  `fsat_to_SAT_seam` + `flatTCC_to_SAT_witness` +
  `flatTCC_to_SAT_reducesPolyMO' : FlatTCC ⪯p' SAT`
  (`Reductions/FSAT_to_SAT_comp.lean`). **The tail is closed; consume
  `flatTCC_to_SAT_witness`/`flatTCC_to_SAT_reducesPolyMO'` from the endpoint
  bridge — do not re-derive anything below it.**
- **The FSAT output codec** (`Reductions/BinaryCC_to_FSAT_free.lean`, 2026-07-05):
  `serF`/`deserF`/`decodeF` (prefix/Polish bit-serialization of the `formula`
  tree) + the PROVEN round-trip `decodeF_serF` + `decodeOut_of_serF` — the
  injectivity backbone of the target-#2 witness's `decodeOut`. This is the
  reusable pattern for any TREE-typed reduction output.
- **The `BinaryCC_to_FSAT` program** (`Reductions/BinaryCC_to_FSAT_free.lean`,
  session 2): `buildFSAT`/`encodeIn` + all emitters (`emitBitsFromScan`/
  `emitBitsFromSent`/`emitCardsAt`/`emitAllSteps`/`readOneFinal`/`emitFinal`) and
  the on-machine guard (`computeWF`/`leCheck`/unary-modulo `dvdCheck`/
  `cardLenCheck`) — pure `Cmd` DATA, `#eval`-validated end-to-end (`FSATSerProbe`
  §4). Do not re-derive; session 3 proves the run/cost lemmas over these.
- **The `BinaryCC_to_FSAT` run-lemma stack** (same file, session 3 parts 1–2,
  all sorry-free & axiom-clean `[propext, Quot.sound]`): `encodeIn_size_le`
  (+ helpers `encodable_size_bitsNat`/`_cardNat`/`_map_*`, `fresh_set_size`,
  `get_unset_of_ne`); the serialization algebra `litFor`/`bitsPrefix`/
  `serF_encodeBitsAt`/`bitsPrefix_append`/`bitsPrefix_take_succ` and its
  card-level lift `cardsPrefix`/`cardsPrefix_append`/`serF_encodeCardsAt`
  (steps/lines/final reduce to the same tag-then-child unrolling one level
  up); the **generic `listAnd`/`listOr` algebras `andPrefix`/`serF_listAnd`
  and `orPrefix`/`orPrefix_append`/`serF_listOr`** (one definition per
  connective serves every level — do NOT re-specialize per level;
  `serF_encodeFinalConstraint` is the `listOr` top closer); the OUT-only
  gadget lemmas `emit{Ftrue,FandTag,ForrTag,False,VarW,LitAt}_run`/`_frame`;
  the fold-invariant templates **`BSInv`** (plain, `emitBitsFromScan_run` —
  now carries a **frame clause**), **`SBInv`** (two-phase sentinel with
  past-the-terminator exit, `emitBitsFromSent_run`), **`RFInv`** (two-phase
  sentinel *parse*, `readOneFinal_run` — outputs `FBITS`/`BLEN`, `SCANF`
  past the terminator), **`CAInv`/`FFInv`** (`nonEmpty`-guarded stream loops
  with black-boxed inner `_run` facts, `emitCardsAt_run`/`emitFinal_run` —
  `FFInv`'s live iteration chains `readOneFinal_run` + `innerFinalSteps_run` +
  `emitFalse`), **`ASInv`/`ALInv`/`FSInv`** (exact-bound nested `listAnd`/
  `listOr` folds with a black-boxed inner-loop `_run`, `emitAllSteps_run`/
  `innerFinalSteps_run`); **`stepBody_run`/`finalStepBody_run`** (var-index
  arithmetic + on-machine bound guard ⇔ `encodeStepConstraint`/
  `encodeFinalAtStep`'s dite); and the register-generic unary loops
  **`unaryMulLoop_run`/`unarySubLoop_run`** (use these at every remaining
  mul/truncated-subtraction site — do not re-derive). **The wellformedness
  guard stack (2026-07-09):** `computeWF_run`, the three checks
  `leCheck_run`/`dvdCheck_run` (reusable pure-arithmetic `DvdArith.subMod`/
  `subMod_eq_mod` unary-`mod` + machine fold `dvdBody_step`)/`cardLenCheck_run`
  (`CLInv` guarded card stream + `cardLenItem_run`/`CEInv` per-item parse), the
  assembly helpers `andFlag_run`/`nonEmptyTFLG_run`, and the spec bridges
  `wf_iff`/`cardsOKB_iff` (`cardsOKB` = the decidable `Bool` card-length flag);
  `computeWF_run` now carries a **frame clause** (its 14-register write set).
  **The assembly layer (2026-07-10):** `precompLen_run` (LREG/LREG1 off INIT)
  and **`buildFSAT_run`** — `(buildFSAT.eval (encodeIn C)).get FOUT =
  serF (BinaryCC_to_FSAT_instance C)` — the correctness crux of the
  `BinaryCC ⪯p' FSAT` witness (`computes` = this + `decodeOut_of_serF`).
  **Factor any monolithic
  emitter into named defeq sub-`def`s (per loop level) BEFORE its run lemma**
  (as `emitFinal` → `finalStepBody`/`finalStepIterBody`/`finalStringBody`);
  the probe stays green (defeq). Copy these shapes; do not re-derive the
  `clear_value`/`heval` bookkeeping.
- **The cost toolkit (2026-07-10-b).** Generic (`Lang/CostFlat.lean`):
  `Cmd.cost_le_flat` (loop-free flat bound over `Cmd.costReads` ceilings +
  growth clause), `Cmd.writes`/`Cmd.eval_get_of_not_writes` (decide-able
  frame), `cost_mulLoop_le`/`cost_tailLoop_le`/`cost_constLoop_le`,
  `Cmd.cost_forBnd_flat_le`, `State.get_length_le_size`. In the witness file:
  the `serF`-length algebra (`serF_length_le_size`,
  `serF_length_le_of_mem_listAnd/Or`, `and/orPrefix_take_length_le`,
  `and/orPrefix_range_succ/_le`, `bitsPrefix/cardsPrefix_take_length_le`,
  `encSList/encCardsOut/encFinal_drop_length_le`, `encSList_length_ge`), the
  WREG transports (`bsBody_WREG`/`sentBitBody_WREG`/`emitBitsFromScan_WREG`/
  `emitBitsFromSent_WREG`/`emitCardsAt_WREG`), the arithmetic closers
  (`mulLoopClose`/`subLoopClose`/`one_le_P`/`le_scale`), and the FULL
  `_cost`/`_effect` stack for every emitter + guard (`emit*_cost`,
  `computeWF_cost`, `leCheck/dvdCheck/cardLen*_cost`, `precompLen_cost`) up to
  the assembly `buildFSAT_cost_le` at the master ceiling `masterOmega`/
  `buildFSATBound`. **The whole `BinaryCC→FSAT` witness `binaryCCFSAT_reductionLang`
  + `binaryCC_reducesPolyMO' : BinaryCC ⪯p' FSAT` is landed & axiom-clean** —
  the mechanical fields (`buildFSAT_usesBelow`/`encodeIn_bitState`/`decode_agree`
  via `Cmd.eval_agree`) are the copy-templates for the next witnesses. Do not
  re-derive.
- **The flatTCC free-reduction stack** (`Reductions/FlatTCC_to_FlatCC_free.lean`):
  `blockMove_run`/`halfMove_run`, `cardStep_step`, `encSList` +
  `encSList_append_inj`, `encKey_injective`/`extractKey`,
  `flatTCC_to_flatCC_correct`.
- **The chain-composition engine** (`PolyTime.lean`): `SeamData`/`comp`,
  `State.get_append_replicate_nil`, `NPhard'`/`NPcomplete'` + bridges.
- **The kSAT3 free-reduction stack** (`NP/kSAT_to_SAT_free.lean`): `kCnf3Check`
  + run lemma + `kSAT3_precomposeData` + `encodeCnf_injective` +
  `encodeCnf_tally_tight` + the `kCheckBudget_le_poly` monomial-domination
  pattern.
- **The free engine** (`PolyTime.lean`): `InNPWitnessLangFree`/`inNPLangFree`
  + `inNPLangFree_to_inNP`, `FreePrecomposeData`/`precomposeFree`,
  `red_inNP_of_langFree`, `reducesPolyMO'_of_langFree`.
- **The verifier stacks** — `EvalCnfCmd.lean` (SAT) and `CliqueRelTM.lean`
  (FlatClique; `readNum_run`/`readNum_cost`/`ltBit_run`, `memberEdge_run`
  nested-loop template, length-only-invariant cost stack).
- **The compiler assembly** (`Compile/`): `run_physical_residue_gen`,
  `compileSeq_sound_physical_residue`(+`_traj`), `compileForBnd_…`,
  `compileIfBit_…`, `bitDecider_run`, `paddedBitDecider_run`,
  `paddedComputeTM`/`paddedCompute_run`; the op gadget stacks; the
  branch/loop/move toolkit; the threading toolkit. ⚠ `Compile_sound`/
  `Compile_run_physical`/`Compile_polyBound` are DEAD/superseded — do not
  attempt to prove.

## Conventions & hard-won gotchas

- **⚠ A `def f : A × B × … → C | (a, b, …) => body` does NOT reduce under
  `unfold f` (2026-07-25).** After `obtain ⟨M, s, …⟩ := x` the goal still shows
  `match (M, s, …) with | (M, s, …) => body`, and `rw [if_pos …]` into `body`
  fails with "did not find an occurrence". Fix: prove the branch equations once
  (`show (if cond then A else B) = _ ; simp [h]` — the `show` IS the defeq step)
  and rewrite with those (`s1Map_pos`/`s1Map_neg` are the model).
- **⚠ `simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]` is
  recursive and eats the WHOLE `&&`-chain, including under `∀ x ∈ l` binders
  (2026-07-25).** So a follow-up `simp only [same set]` on a sub-goal makes no
  progress (a hard error), and any lemma stated about an *unsplit* inner
  `l.all f = true` will never match. Two safe shapes: (a) state per-level
  reflection lemmas (`optAll_iff` for the leaves, `entryB_iff` for the entry
  chain) and `simp only [Bool.and_eq_true, decide_eq_true_eq, <leaf iff>]`
  WITHOUT `List.all_eq_true`; (b) at the top level use explicit `rw` for the
  outer splits (`rw [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq,
  decide_eq_true_eq, List.all_eq_true]`) — a `decide`/`all` sitting as a *Bool
  subterm* of `&&` is not of the form `decide p = true`, so those lemmas cannot
  fire inside the chain. Close the leftover associativity with `tauto`.
- **`Function.Injective f` unfolds with STRICT-implicit binders** — after
  `intro cs; induction cs`, apply the IH as `ih h` (never `ih _ h`, which tries
  to fill the strict implicit explicitly and reports "function expected").
- **⚠ Polynomial size bounds — degree/base discipline (2026-07-24-c).**
  (a) **`ring`/`omega` whnf-TIMES-OUT on `b^k` when `b` is a `set`-let of a
  many-term sum** — the power expands to `C(terms+k-1,k)` monomials (fine at
  `b^6`, dead at `b^8`). `clear_value b` right after `set b := … with hb`; the
  `hb` equation survives and `omega` still uses it for the linear facts, while
  `ring`/`omega` treat `b` as an opaque atom. (b) **A `C·b^d` collapse
  (`d`≤top) OVERSHOOTS `n^d_top` at small `n`** — `102·(n+1)^6 > (n+1)^10`… no,
  `> n^10` at `n=2`; the pure-power upper bound inflates the small-`n` value
  past a tight target. State size bounds at **`(2·(base))^10`** (`= 1024·base^10`)
  so the `2^10` slack absorbs any `C ≤ 1024`, `d ≤ 10` loose bound; still
  `inOPoly`/`monotonic`. (c) For the FINAL `omega` combining `Sg + Σᵢ size(…) ≤
  C·b^d`, **`generalize b^d = P` and each big `encodable.size(…)` atom to a fresh
  var first** — otherwise `omega` tangles the partial power relations (`b`,`b²`,`b^d`)
  and `hb`, and whnf-chokes on the `encodable.size` giants. (d) `length_flatMap_le`
  needs its fiber-bound `c` passed EXPLICITLY (`(… ?_).trans ?_` can't infer the
  middle); for a `≤`-fiber second leg use `Nat.mul_le_mul h (le_refl _)`, for a
  `=`-length second leg `rw [<len eq>]`.
- **⚠ `Var` (= `abbrev Nat`) is OPAQUE to `omega` (2026-07-24).** A register goal
  `(x : Var) < k` makes `omega` treat `x` as an atom it can't relate to `Nat`
  arithmetic — it fails ("No usable constraints") or reports bogus counterexamples
  over metavariable atoms. Retype first: `change (_ : Nat) < _; omega`. When the
  goal is a gadget-lemma register hyp inside an application, drive it with
  `refine <lemma> ?_ … ?_ <;> · change (_ : Nat) < _; omega` — a bare
  `by omega` (or `@lemma … (by omega)`) as a metavariable-typed argument runs
  before the conclusion unifies and fails silently. `Cmd.UsesBelow`/`Op.UsesBelow`
  anonymous-constructor proofs need explicit nesting or `unfold <gadget>` first
  (the whnf that reveals the `∧`-structure does not fire through a bare `def`
  name in term mode).
- **Build:** `export PATH="$HOME/.elan/bin:$PATH"; lake build` (lake **not** on
  PATH; LSP/most MCP can't find it). First build slow — kick off in background.
  Iterate one file directly: `env LEAN_PATH=$(lake env printenv LEAN_PATH)
  lean <file>` (fast, no lake) or `lake build <Module.Name>`. Commit per logical
  step, green. Headline: `Complexity.NP.SAT.CookLevin`.
  The two big witness files are SPLIT (2026-07-17): `BinaryCC_to_FSAT_free`
  and `FSAT_to_SAT_free` each = `*_defs` → `*_run` → original-name
  (cost + witness). Importing the original names still pulls in everything;
  put new codec/def-level lemmas in `_defs`, run lemmas in `_run`,
  cost/witness work in the original module — and keep `_defs` slim, it is
  what lets the two chains build in parallel. Editing a `_run` file
  re-elaborates only it + the modules after it, not a 9K-LOC monolith.
  ⚠ **The lib roots are `Basic`+`Complexity` (`lakefile.lean`), so `lake build`
  only checks modules TRANSITIVELY IMPORTED from `Complexity.lean` — a new
  `.lean` file that nothing imports is INVISIBLE to CI even if it `#eval`s/
  axiom-checks green in isolation.** When you land a new module, add its import
  to `Complexity.lean` (2026-07-12-c caught `FSAT_to_SAT_pre`/`_free` had been
  unimported since 2026-07-12-b). Verify: `find .lake -name "<Module>.olean"`.
- **Probe** a machine/program end-to-end (`#eval`) *before* proving its run
  lemma: `env LEAN_PATH=$(lake env printenv LEAN_PATH) lean probes/X.lean`.
  Probe SEAMS end-to-end too (`FlatCCBinProbe.checkBridge` pattern: assert
  `AgreeBelow` register-by-register on concrete instances).
- **Axiom-check** via a scratch file: `#print axioms <name>` — only
  `propext`/`Classical.choice`/`Quot.sound` for new sorry-free results.
- **`omega` gotchas:** cannot see through `Var := Nat` variables
  (`simp only [Var] at *` first), `var`-typed rcases products — **and (2026-07-12-b)
  any goal whose `</=/≤` CARRIER is the `var` abbrev is silently skipped**
  (`fvar` payloads, `varInCnf` binders: bind `∀ v : Nat, …` explicitly or
  close with term lemmas); **`Nat.max` is an opaque atom** (close `max _ _ < _`
  with `Nat.max_lt.mpr ⟨by omega, by omega⟩`); or
  `encodable.size (n : Nat)` (rewrite with `(fun n => rfl : ∀ n : Nat,
  encodable.size n = n)` first); needs GROUPED products (`2*(P*P)`, never
  `2*P*P`); never splits `(l ++ r).length`; times out on products of two
  non-literal atoms (`generalize` them). **NEW: `omega` whnf-TIMES-OUT when
  `Cmd.cost`/`Cmd.eval` atoms over large states are in scope — fold every
  such atom with `set A := … with hA` + `clear_value A` + `clear hA` before
  calling it. And `omega` hits a hard performance cliff on ~20+-variable
  linear goals — extract a clean-context `private` arithmetic lemma and close
  with `linarith`, or bound componentwise with `gcongr` then `ring`-normalize
  and `omega` on single-variable monomials** (see `binBudget_arith`/
  `binBudget_le_poly`).
- **`l[i]` after a `Cmd.cost` hypothesis = whnf TIMEOUT** — hoist every
  `l[i]`-bearing `have` BEFORE `obtain`-ing a run/cost lemma.
- **`set` retro-folds eval equations but not terms produced by later `rw`** —
  fold new occurrences with `rw [← hs]`. `State.get_set_eq` can't see through
  a `set`-bound local — state a `have` via `rw [hs3]; exact State.get_set_eq
  _ _ _` first. `rw` matches registers SYNTACTICALLY — restate run-lemma
  facts at literal registers (`have hOFF' : State.get T 6 = _ := hOFF`) or
  pass the register explicitly (`State.get_set_ne _ CliqueRelTM.SKIPR _ _ h`).
- **NEW (session 3): plain (non-`omega`) `whnf` TIMEOUT from un-cleared nested
  `State.set` chains.** Threading a fold invariant through ~4+ sequential
  `set wN := w(N-1).set … with hwN` steps (one per `Op` in a straight-line
  body) makes later tactics (`show`, `rfl`, even unrelated `rw`s) try to
  unfold the whole chain back to the root state and time out — **not just
  in `omega`, this hits `rfl`/elaboration generally.** Fix: `clear_value wN`
  immediately after extracting the `get`/frame facts you need from `wN`,
  before introducing `w(N+1)`. The named equation (`hwN`) survives
  `clear_value` and is enough for everything downstream.
- **NEW (session 3): `show`-ing a composed `Cmd.eval` chain equal to a named
  end state is a DEFEQ CLAIM, not automatic — it fails whenever any step's
  `eval` equation was proved (not `rfl`).** Do not write
  `show State.get w5 R = _` hoping the real goal (`State.get ((c1;;c2;;…).eval
  w) R = _`) unifies with `w5` for free. Instead build one explicit
  `heval : (c1;;c2;;…).eval w = w5 := by rw [Cmd.eval_seq, e1, Cmd.eval_seq,
  e2, …, ← hwLast]` (peel one `Cmd.eval_seq` + one step-equation per `Op`,
  finishing with `← hwN` for every gadget-level sub-`Cmd` you black-boxed via
  its own `_run` lemma), `rw [heval]` once, *then* state the per-register
  goals — exactly the `cardStep_card`/`halfMove_run` `show (c1;;_).eval s =
  _; rw […]` pattern, which generalizes to any chain length. **Part-2
  addendum: even the initial `show`-unfolding of the program into its seq
  spine whnf-TIMES-OUT once the body contains a nested `forBnd`**
  (`emitCardsAt`'s body holds two `emitBitsFromSent` loops) — open `heval`
  with `unfold <programDef>` and peel with `rw [Cmd.eval_seq, …]` instead of
  a `show`. Factor every loop body as a named `def` (`sentBitBody`/
  `cardEmitBody`) so `_run` lemmas and `Cmd.foldlState` can name it.
- **NEW (session 3 part 2): `rw [List.replicate_add]` picks the wrong
  occurrence when the LHS replicate's length is itself a sum** (e.g.
  `replicate (a+b) 1 ++ replicate c 1 = replicate (a+b+c) 1`) — use
  `rw [← List.replicate_add]` to fold the append instead. And after
  `rw [<eq ending in serF f>]`, a residual `serF falseFml`/`serF .ftrue`
  literal does NOT auto-close — finish with an explicit `rfl`.
- **NEW (session 3 parts 3–4): more ambiguous-`rw` traps.** (a) In a
  nested-fold step lemma, `rw [List.range_succ]` grabs the goal's *inner*
  `List.range (L+1)` (from the inner-loop `_run` fact) instead of the
  outer `range (j+1)` — unroll the outer one in an isolated
  `have hsnoc : andPrefix ((List.range (j+1)).map g) = …` first, then `rw
  [hsnoc]`. (b) The `show`-as-defeq seq-spine unfolding whnf-times-out even
  for a FLAT body (no nested `forBnd`) once enough state is around — default
  to `unfold <def>` + `rw [Cmd.eval_seq, e1, …]` for every `heval`. (c) A
  `simp only [... State.set_set]`-closed branch whose goal mentions
  `[cond b 1 0]` after `cases b` leaves a `bif`-literal residue — finish
  with `rfl`. (d) When a `set wN`-named state IS the `rw`-target equation's
  RHS, the fold already happened — do not add `← hwN` (it fails with
  "pattern not found").
- **NEW (session 3 part 7): a literal `.set`-chain state (e.g. `encodeIn`)
  elaborates its `.set`s to `List.set`, NOT `State.set`** (the receiver's
  type is the unfolded `State` abbrev at definition time), so
  `State.get_set_eq`/`_ne` do NOT rewrite over it. Don't fight it: every
  `State.get (encodeIn C) r` on such a concrete frame is **definitional —
  close with `rfl`** (the `FlatCC_to_BinaryCC_free` witness fields already
  used this). Inside proofs, states built with explicit `State.set` (`s.set`
  where `s : State` is a variable) still match the `State.get_set_*` lemmas.
- **Multi-case register frames**: `interval_cases r` + per-case
  `repeat first | rw [State.get_set_eq] | rw [State.get_set_ne _ _ _ _ (by
  decide)]` walks any concrete nested-set state (the seam-bridge pattern).
- **`simp` with `List.take_succ` can hit max-recursion in a fat context** — use
  the explicit `rw [List.take_add_one, List.getElem?_eq_getElem hi]` chain.
- **`decide` fails when the goal type mentions free vars** — `show (0 : Nat) ≠ 2`
  first. `Cmd.UsesBelow` of a concrete program: full `simp [defs…]`.
- **`set` (tactic) lives only in `PolyTime.lean`, not `Frame.lean`** (core-only).
- **NEW (session 4, the cost pass):** (a) `Cmd.flatK`/`Cmd.cost` atoms in a
  goal make `omega`/`ring`/`nlinarith` whnf- or isDefEq-TIMEOUT — always
  `set K := Cmd.flatK (…) with hK; clear_value K` (and the same for
  `(Ω+1)^d` power atoms `P2/P3/…`) before the arithmetic closer; keep the
  power-tower equations (`hP3 : P3 = (Ω+1) * P2`) and close with `ring` on
  those + `omega` on the atoms. (b) `nlinarith` in a fat context (a loop
  lemma's 60+ hypotheses) TIMES OUT — extract clean-context `private`
  helpers (`one_le_P`, `le_scale`, `mulLoopClose`, `subLoopClose`). (c) Give
  every `K·(Ω+1)^d` bound Ω=0 HEADROOM (constants like `+16·P4` must cover
  the additive junk at `P4 = 1` — a too-tight constant fails only at Ω=0 and
  omega's counterexample is unreadable). (d) After `rw [Cmd.cost_op]` add
  `simp only [Op.cost]` or the un-evaluated `Op.cost` term poisons `omega`.
  (e) `;;` binds LOOSER than `=`: parenthesize the RHS of every
  `c = (a ;; b) := rfl` restructuring equation. (f) The membership hypothesis
  of `Cmd.eval_get_of_not_writes` is `decide`-able only at CONCRETE registers
  — for symbolic `BASE`, take it as a lemma hypothesis and discharge at call
  sites. (g) `emitFtrue_cost`/`emitFandTag_cost`/`emitForrTag_cost` (= 3) and
  `emitFalse_cost` (= 9) are `rfl`.
- **NEW (2026-07-12, the seam): `injection` on an equation whose CONTEXT holds
  un-`set` composite `Cmd.eval` terms whnf-TIMES-OUT** — it ends up
  symbolically executing the reduction programs (~800K `Nat.rec` unfoldings;
  found by bisect, `set_option diagnostics true` names the culprits). Split
  list equations with `simp only [List.cons.injEq, and_true] at h` +
  `obtain` instead — cheap in the same context. Restating a run-lemma fact
  at a literal register (`have h17 : State.get T 17 = _ := hBOFF`) is a safe
  defeq ascription (register defs unfold; the state arg matches
  syntactically).
- **NEW (2026-07-16, the cost assembly):** (a) the 2026-07-15-b perf
  prescription WORKS and is now the standard for big straight-line cost
  proofs — per-branch `private` lemmas + frame facts precomputed as `private`
  one-liners (each loop write-set `by decide` runs ONCE) + `clear_value`
  after every `set`: `tokenBody_cost` elaborates in ~9s where the monolith
  took >14 min. (b) **`rw [h1, h2] at *` rewrites h1 with itself** (turns it
  into `1 = 1`) — never use `at *` with hypothesis names in the rewrite list;
  distribute per-hypothesis (`rw [Nat.add_mul] at hvar`). (c) `omega` slack
  bounds for `c·X`-vs-junk goals need `27 ≤ X = (E+N+3)³`, not just `1 ≤ X`
  (e.g. `6N+5 ≤ 10X` fails at `X=1`) — bundle `N ≤ X ∧ 27 ≤ X` (`X_facts`).
  (d) distribute `(a+b)*X` with the RIGHT number of `Nat.add_mul` rewrites
  per hypothesis, then `set`+`clear_value` each `flatK·X` product so `omega`
  sees matching atoms on both sides. (e) `Nat.le_self_pow (by omega) _` gives
  `a ≤ a^3` — the cheap way to fund linear-junk-under-cubic bounds.
- **NEW (2026-07-20-b, `inOPoly` closure):** `inOPoly_comp`/`inOPoly_add`
  **UNFOLD `physStepBudget`** (and any def ending in `+ x`) during goal-driven
  unification and split the sum at the WRONG `+`, so `exact inOPoly_add … …`
  against a goal mentioning `physStepBudget` fails with an "application type
  mismatch" showing the budget unfolded. Fix: pass **explicit `(f := …)(g := …)`**
  to `inOPoly_comp`, and build every sum as a `have hsum := inOPoly_add … …`
  (types fixed from the operands, not the goal) then `exact hsum` — the defeq
  check accepts the fold without re-splitting. For a `physStepBudget A B` term
  with non-diagonal args, dominate by its diagonal `physStepBudget M M`
  (`M ≥ A, B`) via `physStepBudget_mono` + `inOPoly_of_le`, then close with
  `(fun m => physStepBudget m m) ∘ M` = `inOPoly_comp M_poly physStepBudget_poly`.
  And a `physStepBudget_mono`-bounded `≤` goal after `refine inOPoly_of_le …`
  is a beta-redex — `show`-restate it before `omega`.
- **NEW (2026-07-20-c, wiring a multi-gadget `Cmd` run lemma —
  `FrontProgram.lean`):** three `omega` traps, all with the SAME misleading
  symptom (`omega could not prove` + a counterexample listing only the ambient
  `hB`/`hxW`, i.e. an *empty* goal model). (a) **An un-ascribed `by omega` as a
  gadget-call ARGUMENT runs against a still-metavariable goal** (`?scan ≠
  ?cnt`) — the explicit register args unify too late. Fix: **type-ascribe every
  one** — `(by omega : (B + 5 : Var) ≠ B + 4)`. (b) **`refine ⟨?_,…,?_⟩ <;>
  omega` and bare `by omega` on a big `∧`-conjunction** hit the same empty-goal
  failure. Fix: prove each conjunct as its own ascribed `have`, or (for the
  final register reads) `by decide` on the constant `≠`s. (c) **After `set sᵢ
  := …`, `omega` whnf-chokes on the `let`-bound state bodies** — `clear_value
  s1 s2 s3 s4` (the `hsᵢ` equations survive) before any `omega`-heavy step. Two
  more: after `set sᵢ`, the gadget's run/frame hyps are **auto-folded to be
  about `sᵢ`** — use them directly, do NOT `rw [hsᵢ]` (unfolding `sᵢ`
  mismatches the folded hyp). And `State.get_set_ne _ _ _ _ h` does NOT match a
  `set`-opaque local (`t0`) — build the copy-block result from explicit `.set`
  terms (state the read `have`s with explicit types so the `_`s unify).
- **NEW (2026-07-16, probing):** `#eval` of a `Cmd` with nested `forBnd`s on
  a >1K-bit stream is OUT OF BUDGET (the budget scan is cubic; the T1 seam
  probe timed out at 10 min) — probe BRIDGES register-by-register on big
  instances and reserve end-to-end `#eval` for small ones. To probe against
  a `noncomputable` map, decode the machine's own output stream (`decodeF`)
  instead of cloning the map.
- **NEW (2026-07-25-b, P+G): `&&` binds LOOSER than `=`.** `a && b = c` parses
  as `a && (b = c)` — every `Bool` identity lemma needs BOTH sides
  parenthesised (`(a && b) = (c && d)`). The symptom is a goal full of
  `decide (x = y)` where you expected `&&`-atoms.
- **NEW (2026-07-25-b): `rfl` for `c.eval s = c'.eval (c₀.eval s)` whnf-TIMES
  OUT even though `Cmd.eval_seq` is `rfl`** — `Cmd.eval` is `Cmd.run`, so the
  defeq check tries to *evaluate* the loops symbolically. Always prove such
  peel equations with `unfold <suffix def>; rw [Cmd.eval_seq]`. Corollary
  shape: name every command suffix as its own `def` and give it a one-line
  `_eval` peel lemma (`S1Parse.pSuf1_eval` …). Then a register that a suffix
  does not write is read off with ONE `Cmd.eval_get_of_not_writes … (by
  decide)` over the whole suffix — the cheapest frame reasoning in the project.
- **NEW (2026-07-25-b): `Cmd.UsesBelow` has no `Decidable` instance** — `by
  decide` fails; use `simp [<every def in the program>, Cmd.UsesBelow,
  Op.UsesBelow, <every register def>]` (the `kCnf3Check_usesBelow` pattern).
  `r ∉ c.writes` at concrete registers *is* `by decide`-able, and cheap even
  for a 1.3K-LOC program.
- **NEW (2026-07-25-b): bundle a multi-register loop invariant as a `def
  … : Prop` plus `_set`/`_frame` transport lemmas** (`S1Parse.EInv`/`SInv`).
  Each program step then becomes one line, and the `by decide` write-set
  memberships are paid once per lemma instead of once per step. This is what
  kept a thirteen-step entry body to ~20 lines of proof.
- **NEW (2026-07-25-b): a big straight-line proof needs `set_option maxRecDepth
  8000`** — the suffix-peel chain exceeds the default at ~10 steps.
- **NEW (2026-07-25-b): `simp` (not `simp only`) on a `Bool` identity turns it
  into a `Prop` conjunction** and then fails; for `&&` reassociation use
  `simp only [Bool.and_assoc, Bool.and_comm, Bool.and_left_comm]`.
- **NEW (2026-07-25-c, `Fin`→`Nat` models): the change-of-variables recipe.**
  A `Fin`-typed nest becomes a machine-shaped `List.range` nest with
  `List.map_coe_finRange_eq_range` (`(finRange n).map (↑·) = range n`) +
  `List.flatMap_map` — packaged as `S1Cards.finRange_flatMap_congr` /
  `map_finRange_congr` (`(∀ i : Fin n, f i = g i.1) ⊢ (finRange n).flatMap f =
  (range n).flatMap g`). Push the flattening through the four list combinators
  with `List.flatMap_append` / `List.flatMap_assoc` / `List.flatMap_map` and a
  hand-rolled `filterMap` lemma. **Enumerations that are not `finRange`**
  (`xOpts`, `pKindList`) need one bespoke `_flatMap` lemma each — state it via
  the *index function* (`kindIdx`) when every consumer is a function of the
  index (`pKindList_flatMap`), and with explicit per-constructor hypotheses
  when a consumer must distinguish constructors (`xOpts_flatMap`, whose
  `Lmove` case needs "is this the boundary marker?").
- **NEW (2026-07-25-c): most cell-code equalities are `rfl`.** `(tCell M b).1`,
  `(hCell M q b).1`, `(bCell M).1`, `(emb M c).1`, `(stateOf M n).1` and the
  whole `cnats ∘ flattenCard` chain reduce definitionally, so a family equation
  is usually `refine finRange_flatMap_congr _ _ _ (fun i => ?_)` nested to
  depth, then `cases mv <;> rfl`. Keep `rOf_eq`/`wOf_eq` as the only
  abstraction barrier (rewrite them on the *model* side, left to right).
- **NEW (2026-07-25-c): `{ e with a := x, b := y }` cannot break the line
  before the first field's column.** Structure-instance fields are parsed with
  `withPosition` anchored at the **first** field, so in `{ cM0 with states := …,`
  a continuation line must be indented past `states`, not past `{`. Symptom:
  `unexpected identifier; expected '}'` pointing at the previous line's end —
  and, worse, an `#eval` that silently uses the un-updated record. Prefer a
  named `def` per record.
- **NEW (2026-07-25-c): `omega` cannot use hypotheses about a `Var`-typed
  variable even after `change (_ : Nat) …`.** A frame lemma
  `(hr : 6 ≤ r ∨ r = 0) ⊢ r ≠ 5` is closed *not* by omega but by
  `rintro k hk rfl` on a decidable disjunction (`k = 1 ∨ … ∨ k = 5`) plus
  `exact absurd h (by decide)`. Also: `by omega` supplied as an *argument*
  (`key 5 (by omega)`) runs against a metavariable goal — hoist every such side
  condition into its own `have`.
- **NEW (2026-07-25-c): `simp [Bool.eq_iff_iff, List.any_eq_true]` loops.** To
  transport a member-wise `Bool` equation across `List.any`, write the two-line
  induction helper instead (`S1Cards.any_key`).
- **NEW (2026-07-25-c, tooling): never build an edit by slicing between two
  `str.index` anchors.** If the anchors come out in the wrong order the slice is
  `""` and `str.replace("", new)` inserts `new` between every character (a
  1.8M-line file). Anchor edits on literal text, or assert `start < end` first.
- **NEW (2026-07-26): a state built as `([] : State).set a x |>.set b y` in a
  PROBE elaborates its `.set`s to `List.set`, not `State.set`** (the 2026-07-12
  gotcha, hit again from the other side) — and `List.set [] 2 v = []`, so every
  register reads `[]` and every check silently prints `false`. Write
  `State.set (State.set ([] : State) a x) b y` explicitly when constructing a
  probe state.
- **NEW (2026-07-26): `rw [if_pos h]` fails when the condition is a `Bool`
  coerced to `Prop`.** `h : (fst && decide (j = 0)) = true` does not match the
  `if`'s decidable instance (the pattern comes out with a doubled `decide`).
  Use `cases hfb : (<the Bool>) with | true => … | false => …` and `simp [hfb]`
  in each branch — `hfb` rewrites the condition to a literal and the `reduceIte`
  simproc finishes.
- **NEW (2026-07-26): `simp only` does not close a goal whose two sides are the
  same STUCK `match`** (e.g. `Op.eval (.head dst src)` after rewriting the source
  register). Finish with an explicit `rfl`.
- **NEW (2026-07-26): an `induction l` INSIDE a `have` whose ambient context
  mentions `l` produces an unusable IH** (`omega` then fails on the fold sums).
  Extract every such induction as a standalone `private` lemma over a fresh list
  variable — `length_eq_sum_ones` / `mul_sum_map` / `trans_sum_le` are the model.
- **NEW (2026-07-26): a `_run` lemma with an 11-register frame chain is a smell.**
  Bundle the dirty set as one `abbrev … : Prop` (`S1Emit.IClean`) and project
  with `hr.2.2.…`; better still define the coarse `EDirty` predicate over the
  whole scratch block once (NEXT TOP-DOWN item 2) so composition is one
  hypothesis per stage. Keep BOTH frame forms available:
  `Cmd.eval_get_of_not_writes … (by decide)` is the cheapest step for a
  CONCRETE register but needs it outside the write set, and a dirty-set-keyed
  lemma cannot serve a concrete register that is merely not written.
- **NEW (2026-07-26-b): `omega` cannot see through a `def`-bound `Nat` bound.**
  `Cmd.UsesBelow_mono (by omega) h` against `6 ≤ s1RegBound` fails with a
  counterexample over the *atom* `↑s1RegBound`. Write
  `(show 6 ≤ s1RegBound by unfold s1RegBound; omega)`. Same family as the `Var`
  opacity gotcha above.
- **NEW (2026-07-26-b): `#eval` aborts on ANY expression depending on `sorryAx`,
  including down a branch it never evaluates.** A skeleton program with one
  `sorry`-ed stage cannot be `#eval`-probed at all, even on inputs that take the
  built branch. Probe the *composition the proof reduces to* instead
  (`probes/S1ProgramProbe.lean` §2), and re-point the probe when the placeholder
  lands. (`#eval!` exists but risks a runtime crash — do not use it in a
  committed probe.)
- **NEW (2026-07-26-b): a sorried `_run` contract is an unchecked assumption —
  probe it.** The assembly typechecks against whatever the contract *says*, so a
  mis-stated placeholder lemma is invisible until the stage is built. Give every
  sorried contract a numeric probe of its conclusion on real instances
  (`probes/S1ProgramProbe.lean` §3–4 does this for `stageC_run`/`stageMYes_run`).
- Methodology: **skeleton-first; refine the highest-risk gap next; decompose
  `sorry`s, don't elaborate them; probe before committing engineering;
  `def`+`sorry` over `axiom` (count = 0); build green between commits.**
