# Plan: hardness for all of NP

## The gap

`cook_levin` proves hardness for `inNPCmd Q`, "`Q` has a verifier *program*". The textbook
hypothesis is `inNP Q`, "`Q` has a verifier *Turing machine*" (`Basic/StringTM.lean`).
`inNPCmd ⊆ inNP` is proved (`inNPCmd_subset_inNP`); the converse is not. Closing the gap
means proving

```lean
theorem inNP_inNPCmd {Q : List Bool → Prop} : inNP Q → inNPCmd Q
```

after which the main theorem can be restated with `inNP` on both sides:

```lean
theorem cook_levin_NP : (∀ Q, inNP Q → Q ⪯p SATStr) ∧ inNP SATStr
```

The register language then disappears from the statement entirely: the reading list of
`cook_levin_NP` is that of `SATStr_inNP` plus `reducesPoly`, and GUIDE §4.3 is no longer
needed. Nothing else in the repository changes.

## What has to be built

Given `inNP Q`, i.e. `R`, polynomials `p`, `t`, a valid single-tape machine `M` and states
`acc`, `rej` with `decidesPairInTime M acc rej R t`, produce an `NPWitnessStr Q`
(`Lang/HardnessStr.lean`). Its fields:

* `rel x c := c.length ≤ p' x.length ∧ R x c`, with `p'` a monotone polynomial majorant of
  `p` (`inOPoly_monomial_bound`, `Reductions/FrontWitness.lean`, gives
  `p n ≤ a·(n+1)^k + b`). The length clause makes `rel` sound for `Q`; `polyCertRel` then
  follows from the `inNP` equivalence, `size_le_two_mul_length` and `length_le_size`.
* `verifier : DecidesLang (fun xc => rel xc.1 xc.2) dBound` with
  `encodeIn (x, c) := certState x ++ certState c`, so `encX := certState`, `xWidth := 1`,
  `encX_canonical := rfl`, `sizeLB := 2 · n`. The program is `simTM M acc p' T` below.
* `dBound`: a monotone polynomial bounding the program's cost (`inOPoly_of_le`,
  `Lang/PolyTime.lean`).

Everything reduces to one program and three lemmas about it.

## The program `simTM M acc p' T`

Input: register `0` = bits of `x`, register `1` = bits of `c`. Constants of the program:
`M` (so `M.sig`, `M.states`, `M.trans`, `M.halt` are fixed data), `acc`, the monomial
`p'` and the monomial `T ≥ t` (again from `inOPoly_monomial_bound`).

**Encoding of the machine configuration in registers.** Let `w := M.sig + 1`.

| register | content |
|---|---|
| `TAPE` | the machine's `right` list, one block of `w` cells per tape cell: symbol `v` is `1^(v+1) 0^(sig-v)` |
| `HEAD` | the head index in unary, `1^head` |
| `STATE` | the state in unary, `1^state_idx` |
| `HALT` | `[1]` once a halting state has been reached |
| `SYM` | scratch: the block under the head, or `[]` for the blank |
| `DONE` | scratch: `[1]` once an entry has fired in the current step |

The block width is fixed per `M`, so equality of two symbols is one `eqBit` on `w`-cell
registers and needs no arithmetic. Blank (`none`) is the empty block, which is what a read
beyond the frontier naturally produces.

**Initialisation.** Write `pairTape x c` into `TAPE`: the block of `3`, then one block per
bit of register `0` (`1 ↦ 1^2 0^(sig-1)`, `0 ↦ 1^1 0^sig`, so a loop over register `0`
with an `ifBit`-guarded constant emitter, `emitConst` in `Reductions/FrontPieces.lean`),
the block of `0`, the blocks of register `1`, the blocks of `0` and `3`. `HEAD := []`,
`STATE := 1^M.start`, `HALT := if M.halt[start] then [1] else []` (a constant).

**Time budget.** `TIMER := 1^(T (|x| + |c|))`: `tallyCells` (`FrontPieces`) counts the two
input registers into a unary tally, `unaryMonomial` raises it to the monomial `T`.

**One step** (`stepCmd M`), run `TIMER` times under `forBnd`, each iteration guarded by
`HALT` (an iteration after halting does nothing, matching `runFlatTM`):

1. *read*: `SYM :=` the block at index `HEAD` of `TAPE`. A loop over `HEAD` drops `w` cells
   from a copy of `TAPE` per iteration (`w` `tail`s), then `w` `head`/`tail` pairs move the
   next block into `SYM`. An exhausted copy yields `SYM = []`, the blank
   (`currentTapeSymbol` returns `none` exactly when `head ≥ right.length`).
2. *select*: `DONE := []`; then, for every entry `e` of `M.trans` **in list order**, the
   fragment "if `DONE = []` and `STATE = 1^e.src_state` and `SYM = block e.src_tape_vals[0]`
   then apply `e` and `DONE := [1]`". Tests are `eqBit` against constant registers filled
   by `emitConst`. First-match order reproduces `List.find?` in `stepFlatTM`. If no entry
   fires the configuration is unchanged, as in `runFlatTM` (`runFlatTM_stuck`).
3. *apply `e`*: `STATE := 1^e.dst_state`. Write `e.dst_write_vals[0]`: rebuild `TAPE` as
   the first `HEAD` blocks, the new block, the remaining blocks after the first `HEAD + 1`
   — with the three cases of `writeCurrentTapeSymbol`: in range (replace), at the frontier
   (append), beyond the frontier or `none` (unchanged). "In range / at frontier / beyond" is
   observed while walking: whether the copy of `TAPE` is exhausted before or exactly when
   the walk ends. Then move: `Rmove` is `appendOne HEAD`, `Lmove` is `tail HEAD HEAD`
   (unary truncated subtraction, exactly `moveTapeHead`), `Nmove` nothing.
4. *halt test*: `HALT := [1]` if `STATE` equals `1^q` for some `q` with `M.halt[q] = true`
   (a fixed disjunction of `eqBit`s against constants, one per halting state).

**Verdict.** `OUTPUT := [1]` if `STATE = 1^acc` and `|c| ≤ p' |x|` (build `1^(p' |x|)`
with `unaryMonomial`, compare with `ltBit`-style consumption, `Lang/NumGadgets.lean`), else
`[0]`. Since `decidesPairInTime` guarantees a halting state in `{acc, rej}` within
`t ≤ T` steps, the verdict is `R x c` conjoined with the length test, i.e. `rel x c`.

## The three lemmas

Let `Repr cfg s` say that `TAPE`, `HEAD`, `STATE`, `HALT` of `s` encode `cfg` as above
(`HALT = [1] ↔ haltingStateReached M cfg`).

1. **`stepCmd_run`**: `Repr cfg s → Repr (cfg' ) (stepCmd.eval s)` where `cfg'` is
   `cfg` if `cfg` is halting or `stepFlatTM M cfg = none`, and the stepped configuration
   otherwise; plus a frame clause for the input registers. Proved entry by entry from the
   definitions of `stepFlatTM`, `applyTransitionEntry`, `tapeStep`; the only tape facts
   needed are the three cases of `writeCurrentTapeSymbol` (`Basic/TapeMono.lean`,
   `MachineFaithfulness.lean`).
2. **`simTM_run`**: by induction on the number of iterations with
   `Cmd.foldlState_range_induct` (`Lang/Frame.lean`) and invariant
   `Repr (runFlatTM i M cfg₀) s`; then `decidesPairInTime` reads off the verdict. This gives
   `Cmd.decides`.
3. **`simTM_cost`**: each iteration costs `O(w · |TAPE| + |M.trans| · (w + states))`,
   `|TAPE|` grows by at most one block per step (`tapeStep_length_le_succ`,
   `MachineFaithfulness.lean`), so the total is `O(T · (n + T))` for `n = |x| + |c|`, a
   polynomial. Tools: `Cmd.cost_forBnd_le` (`Lang/Frame.lean`) with a length-only
   invariant, `Cmd.cost_le_flat` for the loop-free fragments (`Lang/CostFlat.lean`); the
   program depends on `M`, so the decidable certificate `Cmd.chk` does not apply and the
   bound is proved by hand as in `Reductions/FrontWitness.lean`.

`enc_bit`, `usesBelow`, `width_le` are mechanical (every register holds bits; the
register set is fixed).

## Order of work

1. **Interface first.** State `simSpec M acc p' T c : Prop` (the three lemmas as a
   contract over a program parameter `c`), build `NPWitnessStr.ofTM` from it, and prove
   `inNP_inNPCmd` and `cook_levin_NP` *assuming a program with `simSpec`*, the way
   `S1Witness.s1WitnessOf` takes its program as a parameter. This pins every obligation
   and lets the reading list and GUIDE changes be prepared before the program exists.
2. Block gadgets with run and cost lemmas: block emitters, `readBlockAt`, `writeBlockAt`,
   the initialisation of `TAPE`.
3. `stepCmd` and `stepCmd_run` (one transition entry first, then the chain).
4. `simTM`, `simTM_run`, the verdict.
5. `simTM_cost` and the witness fields.
6. Restate the theorem in `Theorem.lean`, extend `ReadingList.lean`
   (`#print_statement_surface CookLevin.cook_levin_NP` prints the list to paste), delete
   GUIDE §4.3 and the corresponding rows of the comparison table, update README.

## Size and risks

Comparable to the front machine and front program (`Reductions/Front*.lean`,
about 2 700 lines): one program generated from a machine, one step lemma, one loop
invariant, one cost ladder. Risks are confined to matching `stepFlatTM` exactly:

* first-match selection over `M.trans` (`List.find?`), reproduced by the `DONE` flag;
* the three write cases and the truncation of `Lmove` at cell `0`;
* `applyTransitionEntry` returns `none` on a length mismatch of the entry's payload lists;
  `validFlatTM` and `M.tapes = 1` exclude this, so the program may assume every entry has
  one write and one move;
* `runFlatTM` stops at a halting state and stays put when no entry matches; both are the
  `HALT`/`DONE` guards.
