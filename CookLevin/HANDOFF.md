# Handoff: S3 migration — loop toolkit complete; `map`-over-lists in progress

## ▶ START HERE (latest pass): finish the `map`-over-lists witness

**What is committed and green** (`lake build` ✅ 3356 jobs, all new names
`#print axioms`-clean):

- The **`forBnd` loop-reasoning toolkit is now complete** in `Lang/Frame.lean`:
  `Cmd.eval_forBnd` (loop = pure state fold `Cmd.foldlState`),
  `Cmd.foldlState_range_induct` (the **invariant principle**),
  `Cmd.foldlState_frame` (registers `≥ k` survive), and
  `Cmd.cost_forBnd_le` (the **cost bound**: invariant `M` + uniform per-iteration
  body-cost `B` ⇒ loop cost `≤ 1 + iters·B`).
- `inOPoly_mul` in `Complexity/Definitions.lean` (products of poly-bounded
  functions are poly-bounded) — needed because an `n`-fold loop with poly
  per-iteration cost has cost `≈ n · poly n`.
- Pair-plumbing combinators `swap` / `map_fst` / `map_snd` (see next section).

**The next concrete step — `map`-over-lists** (gates the whole sound tail: every
chain reduction maps a transform over its cards/clauses). A near-complete draft
is parked at **`parked/MapNatList_WIP.lean`** (NOT built). It targets
`PolyTimeComputableLang' (List.map f : List Nat → List Nat)` from a witness for
`f : Nat → Nat`. **Two hard parts are already proven sorry-free** there:
`mapInv_step` (the loop eval invariant step — peel head element, run sub-witness,
append) and `mapBody_cost_le` (per-iteration cost). What remains is the witness
*assembly* (`normalizes`/`cost_le` wrapper plumbing), which was mid-debug.

### Design (use the identity encoding `LangEncodable (List Nat) = id` first)

Let `k := W.regBound` (the sub-witness's register bound). Registers:
`REM = k` (remaining list), `OUT = k+1` (output accumulator), `counter = k+2`;
result `regBound = k+3`. Element peeling is trivial in the id encoding (each
element is one cell): `head 0 REM` puts `[xs[i]] = enc (xs[i])` in register `0`,
then `W.c` runs there (registers `1..k-1` stay blank — the loop invariant — so
`W.eval_get_of_agree` applies and leaves them blank). `iters = (REM).length =
xs.length` exactly, so the loop needs **no over-iteration guard**.

- **Body** `mapBody W := head 0 k ;; tail k k ;; W.c ;; concat (k+1) (k+1) 0`.
- **Wrapper** `mapNatListCmd W := copy k 0 ;; clear (k+1) ;; forBnd (k+2) k (mapBody W)
  ;; copy 0 (k+1) ;; clear k ;; clear (k+1) ;; clear (k+2)`.
- **Invariant** `mapInv W xs i st := st.get k = xs.drop i ∧ st.get (k+1) =
  (xs.take i).map f ∧ (∀ r, 1 ≤ r → r < k → st.get r = [])` (the last conjunct —
  "low registers blank" — is what keeps `W.eval_get_of_agree` applicable each
  iteration). Drive it with `foldlState_range_induct` (eval) and `cost_forBnd_le`
  (cost), **sharing the same `mapInv`**.

### What remains + the two gotchas you WILL hit

1. **`normalizes` assembly.** Evaluate the wrapper: `copy/clear` give the pre-loop
   state `s0` (with `s0.get k = xs`); `Cmd.eval_forBnd` + `foldlState_range_induct`
   give `mapInv W xs xs.length sL`; then `copy 0 (k+1)` (= `xs.map f` via the
   invariant's `OUT`) and the three `clear`s. Case-split `r`: `r = 0` →
   `xs.map f = enc (List.map f xs)`; `1 ≤ r < k` → invariant's blank; `r ∈
   {k,k+1,k+2}` → cleared; `r ≥ k+3` → `Cmd.foldlState_frame` (then `s0` is blank
   there). The `mapBody` frame bound for `foldlState_frame` must be `k+3` (since
   the counter `k+2` must be `< the bound`), via
   `Cmd.UsesBelow_mono (k+2 ≤ k+3) (mapBody_usesBelow W)`.
2. **`cost_le` assembly.** `mapNatListCmd.cost = 12 + (forBnd …).cost s0` (6 seq
   nodes + 6 unit-cost ops; prove by `rw [Cmd.cost_seq ×6, …]; simp only
   [Cmd.cost_op, Op.cost]; omega`). Bound `forBnd.cost s0` by `cost_forBnd_le`
   with `B := 6 + W.cost_bound (size xs)`. Use `xs.length ≤ encodable.size xs`.
   The remaining glue is `hmul : xs.length * (6 + cb) ≤ (size+1) * (cb+6)` —
   prove via `rw [Nat.add_comm 6 cb]; exact Nat.mul_le_mul (by omega) (le_refl _)`
   (NOT a bare `omega`: it cannot multiply two variables). `cost_bound n :=
   13 + (n+1)*(W.cost_bound n + 6)`; its `inOPoly` uses `inOPoly_mul`, its
   `monotonic` uses `Nat.mul_le_mul`.

**Gotcha A — `omega` and `Var`.** Register indices have type `Var := Nat`, which
`omega` treats as opaque (it reports "no usable constraints" or shows spurious
`↑` coercions). Two safe idioms, both used in the parked file:
  * For a goal like `0 < W.regBound + 2` (Var-typed literal): restate at `Nat`
    (`have e0 : (0:Nat) < W.regBound + 2 := by omega`) and use `e0` by defeq.
  * For a register *variable* `r : Var` with `hge : W.regBound ≤ r`, `hrk :
    r ≠ W.regBound`, … : build `W.regBound + 3 ≤ r` by chaining
    `Nat.lt_of_le_of_ne hge (Ne.symm hrk)` (each step bumps the bound by one),
    and derive disequalities with `Nat.ne_of_gt (Nat.lt_of_lt_of_le _ hge3)`.
  `≠`/`<` between two genuinely-`Nat` terms (e.g. `W.regBound ≠ W.regBound + 2`)
  *do* work with `omega`.

**Gotcha B — `set` only in `PolyTime.lean`, not `Frame.lean`.** `Frame.lean`'s
import context lacks Mathlib's `set`/`ring` tactics (the loop lemmas there were
written core-only). `PolyTime.lean` has them. (The parked file imports
`PolyTime`, so `set` is fine there.)

### After `List Nat`: generalize to the chain types

The chain types (`cnf = List (List (Bool × Nat))`, `cnf × assgn`, the
`FlatTCC`/`FlatCC` cards) use the **generic length-prefixed** encoding
(`instLangEncodableList` / `encListGen`), not the id shortcut. The same loop
structure works, but peeling an element is the `head`/`tail`/`takeAt`/`dropAt`
length-prefix dance (cf. `swap`/`map_fst`), and the invariant uses
`encListGen (xs.drop i)` / `encListGen ((xs.take i).map f)`; you will want a small
`encListGen (L ++ [b]) = encListGen L ++ ((enc b).length :: enc b)` lemma. With a
generic `map` over `LangEncodable α → LangEncodable β`, the cheap sound-tail
reduction `flatTCC_to_flatCC` becomes buildable (it also needs `LangEncodable`
instances for the record types and constant-field injection: `offset:=1` is
`appendOne`, but `width:=3` must be built as the length of a 3-cell scratch list
via `consLen`, since `appendOne/Zero` only emit 0/1).

---

# Handoff: S3 migration — `swap`/`map_snd` witnesses + `forBnd` loop toolkit

## Update: general reduction + loop-reasoning infrastructure

This pass lands the **second concrete non-identity canonical-layer witness** and
the **first fully general (any-predicate) reduction** routed through the layer:

- **`PolyTimeComputableLang'.swap`** (`Lang/PolyTime.lean`, after `constTrueBool`)
  — the witness for pair swap `(x, y) ↦ (y, x)`. An 11-op straight-line program
  (`swapCmd`) that unpacks the length-prefixed product register, rebuilds the
  swapped pair (`enc (y,x) = (enc y).length :: (enc y ++ enc x)`), and clears
  scratch. **All fields proved sorry-free; `#print axioms` = `[propext,
  Quot.sound]`** (cleaner than `constTrueBool`, whose downgrade pulls in the
  bridge). Two private helpers do the work: `swapCmd_eval` (the eval collapses to
  an explicit final state via one `simp only` with the `get_set` + `take_left`/
  `drop_left` set — *no* exponential `set`-chain) and `swapCmd_cost` (constant
  `21`). `normalizes` is a flat register case-split; `usesBelow` is
  `simp only [Cmd.UsesBelow, Op.UsesBelow]; decide`.
- **`reducesPolyMO'_swap` / `reducesPolyMO_swap`** (end of file) — for *any*
  `Q : Y × X → Prop`, `(fun p : X × Y => Q (p.2, p.1)) ⪯p' Q` (and its `⪯p`
  downgrade), via `reducesPolyMO'_of_lang ... (fun _ => Iff.rfl)`. Unlike
  `reducesPolyMO'_trueBool` (correct only for constant predicates), this is
  correctness-preserving for **every** predicate — the first non-vacuous general
  reduction through the canonical layer. Axiom profile matches the existing
  `trueBool` demos (`sorryAx` from the assumed `Compile_sound`, `Classical.choice`).

**Why it matters / how to reuse:** `swap` is the *repack* template (the
data-shuffling counterpart of `map_fst`'s *subroutine-call* template). The sound
tail's reductions rebuild records by permuting/copying fields; `swap` is the
worked example of the no-opaque-sub-witness repack shape, and it validates the
frame toolkit on a program that rewrites register `0` from scratch.

### Also landed this pass: `map_snd` + the `forBnd` loop-reasoning toolkit

- **`PolyTimeComputableLang'.map_snd`** (`Lang/PolyTime.lean`, after `map_fst`) —
  the mirror of `map_fst`: applies `f` to a pair's *second* component. Built
  **definitionally from the combinator algebra** (`swap ∘ map_fst f ∘ swap`), no
  new proof obligations. Axiom-clean. Shows the pair-plumbing combinators
  (`swap`/`map_fst`/`comp`) compose into the layout adapters the chain needs.
- **`forBnd` loop lemmas** (`Lang/Frame.lean`, new "Counted-loop reasoning"
  section) — **the keystone infrastructure that was entirely missing**: before
  this, *no* lemma let you reason about a `forBnd` loop except by unfolding its
  raw `foldl` by hand. Now:
  - `Cmd.foldlState` — the pure-state loop fold (cost dropped).
  - `Cmd.eval_forBnd` — `(forBnd c b body).eval s = foldlState …` (the loop runs
    once per cell of the bound register, counter = unary index).
  - **`Cmd.foldlState_range_induct`** — the loop **invariant principle** (motive
    holds at start + preserved per iteration ⇒ holds at the end). This is the
    workhorse for every future loop-based program.
  - `Cmd.foldlState_frame` — a loop keeps registers `≥ k` if its body/counter
    stay `< k` (the output register survives). All sorry-free, axiom-clean.

**This directly unblocks `map`-over-lists**, which gates the whole sound tail
(`flatTCC_to_flatCC` etc. map a transform over their cards/clauses). The
structural recipe (now that the loop tools exist): the generic list encoding
`encListGen` concatenates `[len_i] ++ enc x_i`, so the **register length is the
total symbol count, not the element count**. `forBnd`'s iteration count is the
bound register's length, so iterate `forBnd` over the encoding register itself
(length ≥ element count) with the body **guarded by an `ifBit` on "remaining is
non-empty"**: peel one element (length-prefix → `takeAt`/`dropAt`), apply the
sub-witness, append to the output, advance the "remaining" register; extra
(past-the-end) iterations are no-ops. The `_range_induct` invariant then carries
"output = map f (first i elements) ; remaining = drop i". This is the next
concrete build; `flatTCC_to_flatCC` additionally needs `LangEncodable` instances
for the record types and constant-field injection (`offset:=1`, `width:=3` — note
`appendOne/Zero` only emit 0/1, so a literal `3` is built as the length of a
3-cell scratch list via `consLen`).

Build green; full project `lake build` ✅. All new public names verified
axiom-clean with `#print axioms` (`swap` / `map_snd` / the loop lemmas show only
`propext` (/ `Quot.sound`); the `reducesPolyMO'_swap` demo matches the existing
`trueBool` profile: `sorryAx` from the assumed `Compile_sound` + `Classical.choice`).

---

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

Additionally, **a first concrete non-identity witness landed**:
`PolyTimeComputableLang'.constTrueBool` for `fun (_ : Bool) => true` — a real
two-`Op` straight-line program (`clear 0 ;; appendOne 0`) with every field
of the canonical-layer witness (cost, normalizes, frame, usesBelow) proved
sorry-free and axiom-clean (no `sorryAx`). It serves as the **template** for
migrating chain reductions: copy the structure, swap in the chain's `Cmd`,
adjust the cost/correctness proofs.

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
