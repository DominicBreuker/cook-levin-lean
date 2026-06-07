# Handoff — the computable layer / compiler (Risk C2)

Authoritative status & the full risk register live in [`../README.md`](../README.md)
and [`ROADMAP.md`](ROADMAP.md). **This file is the working plan for the compiler
(Risk C2)** — the one obligation the whole NP-completeness bridge sits on.

We work **multi-session in two alternating work streams**. At the start of each
session the owner says **`bottom-up`** or **`top-down`**:

- **Bottom-up** — build the gadgets/lemmas the contracts need (the 7 stub ops,
  the loop/branch machines), iterating toward the final proofs.
- **Top-down** — work on the final assembly, *design* its proofs, create
  supporting lemmas with `sorry` (when reasonably provable), and **surface gaps
  early** so we don't waste effort on code that must be discarded.

The two streams **share one interface** — the per-fragment *physical-residue
contracts* and the bridge that consumes them — and meet in the middle there.
Keep both stream sections below concrete and forward-looking.

---

## The bigger picture (read once)

We are proving `theorem CookLevin : NPcomplete SAT`, real and unconditional.
NP-hardness is transported along a chain of poly-time reductions whose **tail**
(`FlatTCC → … → SAT`) is real, done mathematics. The remaining work routes through
one device: **the computable layer** — a tiny structured while-language (`Cmd`/`Op`
with explicit **cost** semantics) compiled **once** to a single-tape `FlatTM`
(`Compile`). Every verifier and reduction is then a short DSL program.

This is **Risk C2**. The live `sat_NP : inNP SAT` and the framework bridges all
reduce to discharging the compiler's physical run contract plus the leaf gadgets.

**The live dependency chain `sat_NP` actually walks (top to bottom):**
```
sat_NP (EvalCnfTM.lean)
  → inTimePolyTM_evalCnf → inTimePolyLang_to_inTimePoly      (PolyTime.lean:140, SORRY — blocked, see WALL)
       → DecidesLang.toDecidesBy   (free encoding)            (PolyTime.lean:125, SORRY — blocked, see WALL)
            → Compile.bitDecider_run                          (Compile.lean ~9486; ✅ migrated to physStepBudget)
                 → Compile_run_physical_residue               (Compile.lean ~9225; PROVEN from the assembly,
                                                               sorry only via the leaf gadgets below)
       evalCnfDecidesLang : DecidesLang …                     (EvalCnfTM.lean:63; SORRY fields: encodeIn_size,
                                                               enc_bit — and now owes regBound/usesBelow/
                                                               noConsLen/width once the bridge is restated)
LEAF GADGETS (the only real remaining math under the assembly):
  compileOp_sound_physical_residue   (Compile.lean:8238; 5/12 ops PROVEN, 7 SORRY)
  compileIfBit_sound_physical_residue  (Compile.lean ~9111; SORRY — gated on real compileTestBit)
  compileForBnd_sound_physical_residue (Compile.lean ~9164; SORRY — gated on real compileForBnd)
```
The **canonical** path (`DecidesLang'` / `inNPLang_to_inNP`) is parallel infra,
not yet on the live `CookLevin` path; it bridges the same `bitDecider_run`.

---

## ⚠ The invariant: `BitState` — LOCKED, do not revisit

The compiled machine has a **fixed 4-symbol alphabet** (`sig = 4`). `encodeTape`
shifts each register cell `+1` (`0→1`, `1→2`), `0` separates registers, `3`
terminates/anchors. A cell `≥ 2` shifts to `≥ 3` and collides with the terminator,
so **every state touching the tape must be `Compile.BitState`** (all cells `∈ {0,1}`,
`Compile.lean:1708`). Numbers are therefore **UNARY** (`enc n = replicate n 1`).
Sound for the size law because `encodable.size Nat = id`: unary length `= n`.
`sig=4`/`BitState`/Option B′ is **owner-settled**; no further design sign-off needed.

---

## ★★ THE WALL — surfaced 2026-06-07 (this top-down pass). #1 cross-stream decision.

The C2 obligation `Compile_run_physical_residue` (correctly) carries
`huses : Cmd.UsesBelow c k` and **`hk : k ≤ s.length`** — it threads `Op.inBounds`
(every per-op gadget assumes its registers already exist on the tape) through the
induction. **But the live and canonical encodings are too narrow to supply `hk`:**

- **Canonical** `LangEncodable.encodeState x = [enc x]` has **length 1**, yet
  composed verifiers use `regBound > 1` (every `precompose`/`map_fst` raises it).
  So `hk : regBound ≤ 1` is **false**.
- **Free / live** `evalCnfDecidesLang` similarly lays its data in a few registers
  while the program touches more.

Two interacting constraints make this a genuine design fork, not a typo:
1. **Register pre-existence.** `Op.inBounds o s` requires `dst/src < s.length`. The
   gadgets navigate by counting `0`-separators; a register past the tape's width
   does not exist to navigate to. (`State.set` auto-pads *semantically*, but the
   *physical gadget* does not create the missing register.)
2. **Tight input encoding.** The framework's `DecidesBy.encode_size` is
   `≤ 2·size + 4` (NP.lean), exactly fitting the canonical 1-register tape. So you
   **cannot** just pre-pad the *input encoding* to `regBound` registers — that adds
   `regBound` cells and busts `encode_size`. (The free path additionally busts it
   already: `EvalCnfCmd.encodeState_size ≤ 5·size+20 ⊄ 2·size+4`.)

**Recommended resolution (bottom-up, clean, eliminates the wall on BOTH paths):**
a **runtime width-padding gadget** that grows the *tape during the run* (appends
empty register blocks up to `k`), tolerant of any starting width. Prepend it inside
`Compile` (using the cmd's static `UsesBelow` bound) or expose a
`Compile_run_physical_residue` variant that pads first. Because the padding is on
the *running tape*, the **input** `encodeTape (encodeState x)` stays length
`2·size+4` (encode_size unaffected!), and after padding `k ≤ s.length` holds, so
`hk` (and `DecidesLang'.reg_width`) can be **dropped** from the contract entirely.
Budget stays poly (`k = regBound` is a per-decider constant added to `G`).

Alternatives, weaker: (a) make *every* per-op gadget auto-create out-of-bounds
registers (more gadget surgery, same effect); (b) relax the framework
`DecidesBy.encode_size` to a per-decider linear `c₁·size+c₂` and pad the input
(ripples to NP.lean:143's product lift; needed anyway for the free path's
`5·size+20`).

Until resolved, the two facts are isolated as `DecidesLang'.reg_width` /
`DecidesLang'.c_noConsLen` (`PolyTime.lean`, `sorry`, fully documented) and the live
`DecidesLang.toDecidesBy` stays `sorry`.

---

## ✅ What this session (top-down, 2026-06-07) did — the budget-shape migration

The C2 obligation was already **proven from the assembly** as the (then primed)
`Compile_run_physical_residue'` with the **correct `physStepBudget` budget**. This
session executed the **GAP-4 ripple** at the compiler→decider boundary:

- **Deleted** the unprimed `Compile_run_physical_residue` (the unprovable
  `overhead (size+cost)` budget — wrong degree AND dropped `s.length`, ROADMAP
  Finding A). **Renamed** the correct lemma to `Compile_run_physical_residue` (now
  THE obligation: `physStepBudget` budget, `UsesBelow`/`k ≤ s.length`/`NoConsLen`).
- **Retargeted `Compile.bitDecider_run`** to consume it: new params
  `(k) (hk : k ≤ s.length) (huses) (hnc)`, budget now
  `physStepBudget (State.size s + s.length + c.cost s + 2) (c.cost s) + 3`. So the
  live decider boundary rests on the **provable** budget shape.
- **Migrated `DecidesLang'.toDecidesBy` / `budget_ge` / `toInTimePoly`** to the new
  budget (encoding/correctness/halting all sorry-free; the only gaps are the two
  pinned `WALL` facts). Added `inOPoly_of_le` (pointwise domination) helper.
- Build green (3358 jobs); `#print axioms CookLevin` unchanged
  (`[propext, sorryAx, Classical.choice, Quot.sound]`).

Net effect: the wrong-budget sorry is gone; the wall it was hiding is now explicit
and pinned. **Do not re-introduce an `overhead`-shaped budget anywhere** — it is
not superadditive and cannot compose (Finding #3 / A).

---

## ✅ PROVEN, reusable — do not re-derive

- **`Compile.run_physical_residue_gen`** (Compile.lean ~9225) — the residue
  induction; `op`/`seq` cases proven, `ifBit`/`forBnd` dispatch to the two
  combinators. W-invariant ① + `physStepBudget` budget ② both threaded.
- **`physStepBudget`** + `_seq` (exact superadditivity) / `_mono` / `_poly`
  (cubic diagonal) — the composable budget. **The only correct budget shape.**
- **`Compile.bitDecider_run`** — decider boundary, now `physStepBudget`. Sorry-free
  except transitively via the leaf gadgets.
- **`compileSeq_sound_physical_residue`** + `_traj` — residue `seq` composition.
- **`Compile.sound_of_run_residue`** — residue run ⇒ `Compile_sound` shape.
- **Threading toolkit** (now all in `Compile.lean`): `Cmd.eval_preserves_BitState`,
  `Op.inBounds_of_UsesBelow`, `Cmd.eval_length_ge`/`_le`, `Cmd.size_eval_le`,
  `State.set_length_ge`, `BitState_set_pad`.
- **Move/branch/loop gadgets:** `moveRegionTM`/`moveRegion2TM` (single/dual FIFO
  transfer), `joinTwoHalts*`, `rewindBracket`/`_transport`, `bitReadTM`,
  `rewindTwoPhaseTM`, `deleteCarryTM`, `navigateAndTestTM`, `loopTM`(+`_run`/
  `_no_early_halt`), `loopBudget_le`. All axiom-clean.
- **5/12 ops PROVEN** in `compileOp_sound_physical_residue`: `appendOne`,
  `appendZero`, `clear`, `nonEmpty`, `head` (each carries the W-invariant ①).

---

# ▶ TOP-DOWN work stream — next steps

You assemble final pieces and design their proofs; create `sorry` lemmas when
provable; surface gaps early.

1. **Drive the WALL resolution (see ★★ above) — highest priority, do FIRST.**
   Confirm the runtime-padding design with a `#eval` probe (does a width-padding
   gadget on a narrow `encodeTape` produce the wider tape the op gadgets expect?),
   then **restate `Compile_run_physical_residue`** to drop `hk : k ≤ s.length`
   (pad internally from `UsesBelow c k`). This deletes `DecidesLang'.reg_width` and
   unblocks the canonical bridge. Coordinate with bottom-up (who builds the pad
   gadget). If you instead go the encode_size route, that touches NP.lean.
2. **Close the live free bridge `DecidesLang.toDecidesBy` / `inTimePolyLang_to_inTimePoly`.**
   AFTER the wall resolution (it determines the fields): add to `DecidesLang` the
   `regBound`/`usesBelow`/`noConsLen` (and, only if padding the input, a width
   field), thread them into `bitDecider_run`, and restate the budget as
   `physStepBudget`-shaped (mirror `DecidesLang'.toInTimePoly`; `inOPoly_of_le` +
   `physStepBudget_poly`/`_mono` are ready). This is the path `sat_NP` walks.
   ⚠ Also needs the framework `DecidesBy.encode_size` (`2·size+4`) loosened for the
   free path's larger linear encoding — decide this with the owner.
3. **Retarget the reduction side** (`Compile_sound`, Compile.lean:8750, still an
   independent `sorry`; `PolyTimeComputableLang.toFrameworkWitness'`,
   PolyTime.lean) to the `physStepBudget` budget via `sound_of_run_residue` + the
   new `Compile_run_physical_residue`. Lower priority (not on the live in-NP path).

# ▶ BOTTOM-UP work stream — next steps

You build the gadgets the (pinned) contracts need. Build green per item;
`#print axioms`-clean. Probe each machine end-to-end (`#eval`) before proving.

1. **Build the runtime width-padding gadget (NEW — unblocks the WALL).** A gadget
   that, on a tape narrower than `k` registers, appends empty register blocks (one
   `0`-separator each) until the tape has `≥ k` registers, head rewound, tolerant
   of any starting width. Prove its run/`_no_early_halt`/budget. This is the
   shared rendezvous with top-down step 1.
2. **Task 1 — unary encodings + scratch operands** (gates all 7 ops). Restate
   `takeAt`/`dropAt`/`consLen` unary (length = the register's unary count, not
   `headD 0`); bump `consLen`'s `Op.cost`; add empty-scratch operands
   (`copy`/`tail`/`concat` need 1, `eqBit` needs 2); re-lay `Nat`/product/`List`
   encodings bit-level + `BitEncodable` instances; **re-lay `EvalCnfCmd.encodeState`
   UNARY** (the LIVE `sat_NP` encoding, cells `v+3`/`2` today) and discharge its
   `enc_bit` / `encodeIn_size`. After this, `consLen` preserves `BitState` and the
   `NoConsLen` side-condition (`DecidesLang'.c_noConsLen`) is **dropped entirely**.
3. **The 7 op gadgets** in `compileOp_sound_physical_residue` (Compile.lean
   ~8238): `copy`/`tail`/`concat` via `moveRegion2TM`; `eqBit` via compare-and-
   delete (2 scratch); `takeAt`/`dropAt` via counter-bounded transfer over
   `lenReg`; `consLen` unary. Each must establish the W-invariant ①
   (`State.size(out) + |res_out| ≤ State.size s + |res_in| + Op.cost o s`).
4. **The two stub machines (gate the `ifBit`/`forBnd` combinators):**
   - `compileTestBit t` (Compile.lean:1483): navigate to register `t` + `bitReadTM`,
     two-exit tester; then prove `compileIfBit_sound_physical_residue` via
     `branchComposeFlatTM_run` + `joinTwoHalts` + the rewind bracket.
   - `compileForBnd counter bound body` (Compile.lean:1631): a `loopTM` over the
     bound's unary length; then `compileForBnd_sound_physical_residue` via
     `loopTM_run`/`_no_early_halt` + the body's residue contract.

---

## Conventions & hard-won gotchas

- **Build:** `export PATH="$HOME/.elan/bin:$PATH"; lake build` (`lake` is **not** on
  PATH; LSP/most MCP features can't find it). First build slow (~minutes); iterate a
  single module with `lake build Complexity.Lang.Compile` / `…PolyTime`. Commit per
  logical step, green. Headline module: `Complexity.NP.SAT.CookLevin`.
- **Probe** a built machine end-to-end *before* proving its run lemma:
  `env LEAN_PATH=$(lake env printenv LEAN_PATH) lean /tmp/x.lean` with
  `import Complexity.Lang.Compile`, `open Complexity.Lang`,
  `runFlatTM N M { state_idx := M.start, tapes := [([], 0, Compile.encodeTape s)] }`.
  Every gadget exits with its head on the trailing terminator — rewind-bracket.
- **Axiom-check** via a scratch file: `#print axioms <name>` — must show only
  `propext`/`Classical.choice`/`Quot.sound` for new sorry-free results.
- **Budget:** only `physStepBudget` composes. Never an `overhead`/`(·+1)²` shape.
- **Append a BIT `b`** = `appendAtTM (b+1)`. `deleteCarryTM` deletes the cell **left
  of the head**; `navigateAndTestTM src` lands the head **on** src's first content.
- **`omega` can't see through `Var := Nat`** (use a `Nat`-typed param), record
  projections / `def`-constants (`show` the reduced form first), nor a `set x := e`
  for hyps created *after* the `set`. **Avoid nested `set`/`let` over `State.set`/
  `.get`** (`isDefEq` blows up ×8/level — flatten with `simp only [Cmd.eval_op, Op.eval]`).
  **`.get` mis-resolves on `State` literals** — write `State.get s r` explicitly.
- **A polymorphic structure field over `encodeState` needs `∀ x : X`** (annotate the
  binder) or inference loops.
- Methodology: **skeleton-first, refine the highest-risk gap next, decompose
  `sorry`s don't elaborate them, probe before committing engineering, `def`+`sorry`
  over `axiom` (count = 0), build green between commits.**
