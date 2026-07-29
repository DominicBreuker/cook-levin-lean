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

## Where the proof stands (2026-07-29)

**The hardness half of Cook–Levin is proven modulo ONE `sorry`: the S1 program's
cost ladder.** The program is finished and axiom-clean; the ladder is a
**purely structural** obligation and is now down to **one gadget**.

```
FrontS1Comp.SAT_NPhard''_of_S1 (c : Cmd)
  (hcomputes : ∀ x, s1Extract (c.eval (headEncodeIn x)) = s1Key (S1Map.s1Map x))
  (huses     : Cmd.UsesBelow c S1Program.s1RegBound)
  (hcost     : S1Witness.S1CostBound c)
  : NPhard'' SAT
depends on axioms: [propext, Classical.choice, Quot.sound]
```

| piece | status |
|---|---|
| sound tail, front (C8-0…C8-5), tableau maths + both size bounds | ✅ axiom-clean |
| S1 map + guard + correctness iff + output bound | ✅ |
| S1 program, all stages, `stageC = cFive ;; stepFam ;; cPrelude` | ✅ **ALL BUILT** |
| `s1Program_computes` / `s1Program_usesBelow` | ✅ axiom-clean |
| `Cmd.PolyCost` (`Lang/CostPoly.lean`), `Cmd.CapCost` (`Lang/CostGrow.lean`) | ✅ **both sorry-free** |
| **the cost ladder** `S1Witness.s1Program_costLeSize` | ❌ **the only open S1 item — 2 loops** |
| `inNPLangFreeSplit SAT` (⇒ `NPcomplete'' SAT`) | ❌ open, top-down, independent |

**Sorries in built code: 6** (unchanged) — five pre-existing (`red_inNP`'s
`inTimePoly` half; `hasDeciderClassical`; 3× `MultiToSingle`, dead code) and
`S1Witness.s1Program_costLeSize`.

## ★ Latest session

**2026-07-29 (bottom-up) — a cost layer that survives a loop; the residual is
now TWO loops in ONE gadget.**

New: `Complexity/Lang/CostGrow.lean` (sorry-free, axiom-clean) and
`probes/S1GrowSafeProbe.lean`. `S1Witness.s1Program_polyCost` is **gone**,
replaced by `s1Program_costLeSize` (same content, stated in the shape the new
layer produces); `s1CostBound_of_costLeSize` is the new bridge and
`s1CostBound_of_polyCost` / `s1CostBound_of_capChk` both route through it.

⚠ **FINDING Z — a ONE-cap cost predicate cannot survive a loop, and that is why
`Cmd.PolyCost` stalled at 96%.** `PolyCost`'s cap is a single `M` over
`c.costReads`. After one loop iteration the body's outputs are bounded by
`poly(M)`, so the next iteration's cap is `poly(poly(M))` and `m` iterations
give a **tower**. `Cmd.polyCost_forBnd` avoids this only by *forbidding* the
body to write what it cost-reads — which is exactly the 4% residual. The fix is
to split the cap in two, and it is not cosmetic: it is what makes the loop rule
non-compounding.

**Endpoints to consume — do NOT re-derive:**

* **`Cmd.CapCost c F F'` := `∃ K D, ∀ s MF N, (F-registers ≤ MF) → (all ≤ N) →
  cost ≤ K·(MF+1)^D·(N+1) ∧ (∀ r, |eval@r| ≤ N + K·(MF+1)^D) ∧
  (∀ r ∈ F', |eval@r| ≤ MF + K·(MF+1)^D)`.** Closed under `CapCost.seq`,
  `.ifBit`, `.mono`, `capCost_op` and **`capCost_forBnd`**.
  * the **cost** may be linear in `N` — that is what pays for FINDING X, the
    `copy EOUT_C EOUT_C` no-op, for free, with no pinned `_run` lemma re-opened;
  * the **growth** may not depend on `N` — that is what stops compounding;
  * with `bnd ∈ F` the trip count is `≤ MF`, so `N_m ≤ N + MF·poly(MF)`.
* **`Cmd.NoGrow c r`** — `|c.eval s @ r| ≤ max |s@r| 1`, an **idempotent** bound,
  so a `NoGrow` body may be iterated *any* number of times. This is what covers
  the drained cursor `forBnd idx SCAN (… tail SCAN SCAN …)`, whose own bound
  register is the one being consumed.
* **`Cmd.GrowOk c r F`** — `|c.eval s @ r| ≤ |s@r| + poly(MF)`, per register,
  against a set `F` the command never writes. Deliberately **flow-insensitive**
  and **total**: a loop contributes nothing to `r`'s growth unless it writes `r`,
  so a register can be certified *before* the loops around it are analysable.
  That independence is the whole point of `Cmd.promote` — and, see below, also
  its limit.
* **`Cmd.promote F cnt body`** — the registers a loop body writes but still
  leaves capped. A written register cannot join the frozen set naively (its cap
  would have to satisfy `MF' ≥ MF + m·P(MF')`, which has no polynomial
  solution); `GrowOk` buys the invariant against the *strictly* frozen set, and
  the body's own `CapCost` then spends it. Round 0 buys, round 1 spends; both
  runs are over the same body and the same states, so nothing is circular. This
  is what lets `S1CardEmit.CH` and `S1Emit.EC` — advanced by `tallyReg` inside
  the very loop that then uses them as an inner trip bound — work at all.
* **`Cmd.capChk : List Var → Cmd → Option (List Var)`** — the decidable forward
  pass; `Cmd.capCost_of_capChk` is its soundness and
  **`Cmd.costLeSize_of_capChk c F (by decide)`** is the one-liner.
* **`S1Witness.costRegs = List.range 60`** — the seed set. At program entry every
  register is bounded by the input size, which is what
  `Cmd.CapCost.cost_le_size` needs.

**Measured (`probes/S1GrowSafeProbe.lean`):** `capChk costRegs` accepts
`stagePG` (30 loops), `stageSig`, `stageInit`, `stageFin`, `stageMYes`,
`stageMNo` and **`S1CardEmit.cFive`** (81 loops, three levels — the family that
exercises all three shapes the 2026-07-28-c probe found unsafe). It rejects
**exactly two loops**, both in `S1StepLoop.scanSeen`:

```
(43, 46) = forBnd EK1 SSEEN scanBody          -- the dedup scan
(42, 22) = forBnd SIX  EE   … (inside readItem TJ1 EE SIX in scanBody)
```

`badLoops` over the **whole** `s1Program` returns exactly those two, so no other
loop in the program is rejected.

⚠ **TWO PERFORMANCE FACTS, and do not confuse them.**
* The kernel `decide`s `capChk` on the whole `s1Program` in **19 s** — but that
  run **short-circuits**: `Option.bind` hits `stepFam`'s failure before reaching
  `cPrelude`. It is *not* evidence that a successful whole-program run is fast.
* `S1Prelude.cPrelude` alone did **not** finish in 10 minutes, by `#eval` or by
  `decide`. `capChk` recomputes `Cmd.writes` over the whole subtree at every
  loop level and runs `Cmd.GrowOk` once per candidate register per loop, so it
  is superlinear in nesting depth, and `cPrelude` is the deepest nest in the
  program.

**Budget a slot for this**: represent register sets as a `Nat` bitmask
(`Nat.testBit` / `|||` / `&&&` are GMP-accelerated in the kernel; every register
is `< 64`) and hoist `Cmd.writes` so it is computed once per node rather than
once per enclosing loop. Do it *before* the merged pass, not after — the merged
pass will make the analysis heavier still.

## NEXT BOTTOM-UP session — close the last two loops, and nothing else

Both rejections have one cause. `SSEEN` (the dedup seen-set) is genuinely
`≤ poly`: the entry loop runs `≤ |PNTRANS|` times and each iteration appends one
capped key via `Cmd.op (.concat SSEEN SAX SSEEN)`. `Cmd.promote` cannot certify
it because `Cmd.GrowOk` is flow-**insensitive** and `SAX` is *built earlier in
the same body* (`pushKey`: `clear SAX ;; appendOne SAX ;; concat SAX SAX SKQ ;;
…`), so `SAX ∉ freezeFor F cnt body`. Cap `SSEEN` and both loops close.

**The fix: a flow-sensitive growth pass, merged with `capChk`.**

Replace `GrowOk`'s role in `Cmd.promote` by a single forward analysis returning
**a pair**: the capped set (as `capChk` already does) *and* the set of registers
whose growth so far is certified additive. Threading the capped set is what lets
`concat SSEEN SAX SSEEN` be accepted once `SAX` has been capped by the
straight-line prefix.

⚠ **Three traps, all found on paper this session — do not re-discover them:**

1. **The merged pass must not hard-fail on a loop with an uncapped bound.** It is
   used *inside* `promote`, so it runs before the loop bounds are known good. At
   such a loop it must return a conservative result (capped-after `= ∅`, growth
   `=` the `NoGrow` set) rather than `none`. Sound, because it claims less.
2. **`Cmd.growOk_sound` requires `F` to be UNWRITTEN by the command** (`hfr`) —
   the `seq` case re-establishes the cap with `Cmd.eval_get_of_not_writes`. So
   you cannot simply feed promoted (hence written) registers back into `GrowOk`.
   The one safe relaxation is `NoGrow` members: `|c.eval s@v| ≤ max |s@v| 1`
   survives a `seq`, so `Cmd.freezeFor` may be widened to
   `(cnt :: F).filter (fun v => !body.writes.contains v || body.NoGrow v)` with
   the cap becoming `MF + 1`. That alone gets `SCUR` frozen (it is drained by
   `tail SCUR SCUR`) — **but it does not close `SSEEN`**, because `SAX` is not
   `NoGrow`. Do it anyway: it is cheap and strictly widens the analysis.
3. **Iterated promotion (`promote` run to a fixpoint) does NOT work**, for
   exactly reason 2: rounds 2+ would need `GrowOk` over a frozen set containing
   written registers (`SKQ`, `SAX`). The chain here is 4 deep — `SCUR` →
   `SKQ`/`SKT`/`SKV` → `SAX` → `SSEEN` — so this is not a corner case. Only the
   merged flow-sensitive pass reaches it.

**Order of work.** (a) make the checker fast (bitmask register sets, hoisted
`Cmd.writes`) and re-run `probes/S1GrowSafeProbe.lean` §1 — without this you
cannot even *measure* `cPrelude`; (b) widen `freezeFor` per trap 2; (c) build the
merged pass and prove its
soundness by the same shape as `Cmd.capCost_forBnd` (one
`Cmd.foldlState_range_induct` whose motive carries the frame equality, the
per-stratum caps and the global cap — that proof is already written and is the
template); (d) `s1Program_costLeSize := Cmd.costLeSize_of_capChk _ costRegs (by
decide)` and delete the `sorry`.

⚠ **Never `sorry` the Boolean `(s1Program.capChk costRegs).isSome = true`** — it
currently evaluates to `false`, so that would be asserting a falsehood. The
`sorry` lives on `s1Program_costLeSize`, which is *true*.

**Fallback if the merged pass stalls (est. half a session):** prove
`Cmd.CapCost S1Step.scanSeen F F'` by hand — `scanSeen` reads `SSEEN`, writes
`EE`/`SKP`/`CX`/`TJ1`–`TJ3`, and its `_run` lemma (`scanSeen_run`) already pins
everything. Then glue with `CapCost.seq`/`.ifBit`/`capCost_forBnd` up through
`entryPre` → `entryBody` → `stepFam`, and `capChk (by decide)` for the rest. The
gluing needs the intermediate `F` sets named; get them from
`#eval Cmd.capChk costRegs <gadget>`.

When it lands, `S1Witness.s1_reductionLang`, `s1_reducesPolyMO'`,
`S1SATComp.s1_to_SAT_reducesPolyMO'` and **`FrontS1Comp.SAT_NPhard''`** all
become axiom-clean in one step. Check with a scratch `#print axioms` file (or
top-down item 1) and update the README/ROADMAP status tables.

**Do NOT** re-open `s1Key`, `s1RegBound`, `EScratch`/`CDirty`, `stageC_run`'s
statement, the two seams' scrub ranges, `S1Step.stepSeg`/`stepEmit`'s contract,
or the entry loop's register table — and do **not** swap the `copy r r` no-op
(FINDING X; `CapCost` makes it free). Stage C's 30-register licence is
**exactly** exhausted.

## NEXT TOP-DOWN session — the membership half, then the headline

Hardness is one gadget away, so the top-down critical path is the other half of
`NPcomplete'' SAT`. All items below are independent of the cost ladder
(different files), so a top-down agent can run in parallel with a bottom-up one.

1. **A `#print axioms` regression list — do this one first, it is cheap, and it
   is the tripwire for the cost ladder.** `probes/AxiomProbe.lean` listing the
   ~30 endpoint names (`S1Program.stageC_run`, `s1Program_computes`,
   `s1Program_usesBelow`, `S1Step.stepFam_run`, `entryPre_run`, and now
   `Cmd.capCost_of_capChk`, `Cmd.capCost_forBnd`, `Cmd.growOk_sound`,
   `Cmd.get_length_eval_le`, `S1Witness.s1CostBound_of_costLeSize`) would catch
   an accidental `sorryAx` inheritance in one run — exactly what the
   placeholder-quantification discipline protects and nothing currently verifies
   (standing risk #7). **It also tells you the moment the ladder lands.**
2. **`inNPLangFreeSplit SAT` — the last piece of `NPcomplete'' SAT`, and the
   top-down critical path.** The live SAT verifier does not factor verbatim as
   a Split witness: `assgn` certificates are `List Nat` (sentinel-unary),
   `InNPWitnessLangFreeSplit.rel` wants `List Bool`, and `encodeState` has 8
   trailing scratch `[]`s *after* the certificate register (so
   `encodeIn (x,c) = encX x ++ certState c` fails on the layout, not on the
   mathematics). The adaptation is a **`DecidesLang.FreePrecomposeData`**: trim
   the trailing `[]`s and prepend a bits→sentinel decode `Cmd`. Template:
   `NP/kSAT_to_SAT_free.lean`'s re-encoder. Probe the layout first
   (`probes/SATSeamProbe.lean` has the decode helpers) — the risk is that
   `certState`'s width is not a per-witness constant, which would break
   `xWidth`. With it, `NPcomplete'' SAT = ⟨FrontS1Comp.SAT_NPhard'', that⟩.
3. **Swap the headline** once (2) lands: state `CookLevin'' : NPcomplete'' SAT`
   next to the legacy `CookLevin`, and only then delete the legacy `⪯p` front
   (`GenNP_is_hard.lean`, `L_to_LM`/`LM_to_mTM`/`mTM_to_singleTapeTM`,
   `Simulators/MultiToSingle.lean` — that IS the S2 collapse, and it retires 4
   of the 6 remaining sorries). ⚠ Do the deletion as its own commit, after the
   new headline is green: `CookLevin` is what the README's status table quotes.
4. **The honesty audit of the composed chain** (standing architecture risk #1;
   never done end to end). Six witnesses now compose into one: check each
   `encodeIn` is the natural layout of its *input* type, each `decodeOut` the
   inverse of the natural *output* layout, and that no reduction work hides in
   an `encodeIn`. The two head seams are pure scrubs by construction
   (`clearRange` only clears), so the audit is really about `WQ.encodeInQ` (the
   extra unary size register at `xWidth` is the verifier's own `encX` plus
   `1^(size x)`, which the front program *consumes* — layout, not work) and the
   four older witnesses. ⚠ **Add one item**: `S1CostBound`'s `cost_bound` is now
   an anonymous `Exists.choose`, so confirm nothing downstream depended on
   `s1_reductionLang.cost_bound` being *definitionally* `S1Map.s1Bound` (the
   whole project builds, so nothing does — record the verdict). Write the
   verdict into the ROADMAP risk register.
5. **Also independent and cheap:**
   * re-run `probes/SeamS1Probe.lean`, `probes/S1PreludeProbe.lean`,
     `probes/S1PreludeEmitProbe.lean`, `probes/S1StepModelProbe.lean`,
     `probes/S1StepEmitProbe.lean`, `probes/S1StepLoopProbe.lean`,
     `probes/S1CardEmitProbe.lean`, `probes/S1CardModelProbe.lean` after any
     register-frame or model touch (⚠ `S1PreludeEmitProbe` takes ~6 min and
     `S1StepLoopProbe` ~3 min: the emitter appends cell by cell, so interpreting
     it is quadratic — keep every new probe instance at `σ ≤ 1`);
   * **S3 retirement bookkeeping**: the honest `⪯p'`/`NPhard''` line is now
     end-to-end, so the ROADMAP's S3 entry can be re-scoped from "must be
     built" to "must be *switched to*, then the old one deleted" — write down
     exactly which declarations still mention `reducesPolyMO`/`NPhard` on the
     proof path.
   * `probes/S1CardEmitProbe.lean` §1 still asserts `cFive`'s output is a
     *prefix* of `encNats (cardBlocks M)`; `probes/S1StepLoopProbe.lean` §1 now
     asserts the full equality for `stageC`, so the older section can be
     retired or re-pointed.

**Recommendation: run a BOTTOM-UP session next.** The cost ladder is two loops
from done, the residual has a single named cause and a designed fix, and the
whole-program `decide` is already fast enough. Top-down item 1 is a 30-minute
warm-up for either stream; top-down item 2 is the right pick for a parallel
agent.

## The S1 register frame — PINNED

```
stage P/G (Reductions/S1Parse.lean)
0  ZERO (andIn no-op target; ends [])   6  PSIG      12 PNTRANS   17 FLG
1  MREG (in) / SIGMA (out)              7  PTAPES    13 PTRANS    18 VAL
2  SREG (in) / INIT  (out)              8  PSTATES   14 SCAN      20 RES
3  1^maxSize (in) / CARDS (out)         9  PSTART    15 HEAD  ⊘   21 ONE
4  1^steps   (in) / FINAL (out)        10  PNHALT    16 INBLK ⊘   23 TSCAN
5  STEPS (out)                         11  PHALT     22 LT_B  ⊘   24 NEF
                                                     26 SKIPR ⊘   27–31 I1–I5
the emitters (Reductions/S1Emit.lean)     stage C (Reductions/S1CardEmit.lean)
32 EOUT_S  Σ's output (1^PSg)             14 CBV  1^(bv sig states)
33 EOUT_I  I's output                     18 CS1  1^(sig+1)
34 EOUT_C  C's output                     19 CS2  1^(sig+2)
35 EOUT_F  F's output                     20 CQ1  1^(states+1)
36 EOUT_T  1^(steps+1) (stage M)          21 CX   1^(xv sig states x)
37 ESG  1^(Sg M)   42 EE  scratch         23 CH   1^((sig+1)(q+1))
38 EA / 39 EB / 40 EC / 41 ED             24 CD   the draining PHALT
43 EJ1 / 44 EJ2 / 45 EJ3  counters        25 CE   the popped halt bit
46 EK1 / 47 EK2  scratch                  27 CZ   [] (the zero source)
s1RegBound = 48
```
`32`–`36` persist to stage M; `37`–`47` are scratch every stage reuses. Stage C
reuses the P/G block `[14,32)` for its constants (it is free once stage G has
run) and `EE`/`EJ1`–`EK2` for its counters; `S1Program.cFive_frame` proves that
set sits inside `CDirty`. The two seams scrub against `s1RegBound = 48` and the
tail composite's `57` — **changing `s1RegBound` means changing
`S1SATComp.scrub4` and re-running `probes/SeamS1Probe.lean` §1.**

**Stage C's prelude family (`S1Prelude.lean` + `S1PreludeEmit.lean`) — PINNED
and BUILT. `PPAᵢ` holds `1^pav` (`pav = base` for a star kind, `base + add`
otherwise) and `PJᵢ` is owned by the resolution level alone — see FINDING G:**

```
14 PBV  1^(bv σ st)      19 PKV2 1^k₂    23 PKV3 1^k₃    28 PJ1 res level 1's j
15 PKV1 1^k₁             20 PST2 star?   24 PST3 star?   29 PJ2 res level 2's j
16 PST1 star?            21 PPA2 1^pav   25 PPA3 1^pav   30 PJ3 res level 3's j
17 PPA1 1^pav            22 PKC2 band    26 PKC3 band    31 PCS2 cut-seen → 2
18 PKC1 band counter     27 PZ   []                      38 PCS3 cut-seen → 3
37 ESG 1^(Sg M)=1^sgv   39 PHB 1^(hv σ q0 0)   41 PQ0 1^q0    43 PCN preamble cnt
40 PB5 1^5              42 PDR the min drain   44 PA1 1^(q0+1) 45 PA2 1^(σ+1)
46 EK1 tally + block cnt 47 PFL preamble flag  34 EOUT_C the output
```
`PCS3 = S1Emit.EA` is a deliberate reuse of `loadSg`'s scratch, dead once the
preamble has finished. `S1Prelude.PDirty` is the list, `PDirty_cdirty` the proof
it is inside the licence, `probes/S1PreludeEmitProbe.lean` §3 the numeric check.

**Stage C's `stepBlocks` family (`S1StepEmit.lean` + `S1StepLoop.lean`) —
PINNED and BUILT. It emits *before* the prelude, and `pPre` rebuilds every
constant the prelude's nest reads, so the two frames need not agree (FINDING E,
weakened). ⚠ These 30 registers are ALL of `S1Program.CDirty`: the licence is
now EXACTLY full, so a new gadget here must reuse, never claim:**

```
constants (SConst, established by cFive — S1Step.SConst_of_cFive, free)
14 CBV 1^(bv σ st)   18 CS1 1^(σ+1)   19 CS2 1^(σ+2)   27 CZ []   6 PSIG 1^σ
per entry (SEntry, published by S1Step.entryPre)
20 TQ  1^((σ+1)(q+1))   23 TQ2 1^((σ+1)(q'+1))   24 TR  1^(rOf σ mT mV)
25 TW0 1^(wOf … false)  17 TW1 1^(wOf … true)    39 TFN "mv=2"  40 TFR "mv=1"
written by the entry body — SD3 = [TJ3,EK1] ⊂ SD2 = [TJ2,TJ3,EK1] ⊂ SD1
21 CX 1^(xv σ st x)  28/29/30 TJ1/TJ2/TJ3 counters  42 EE  46 EK1  34 EOUT_C
the entry loop (S1StepLoop.lean; LD = all of the above minus SConst, plus:)
41 SCUR  the PTRANS cursor        43 SSEEN the seen-key stream (encSyms, PREPEND)
44 SCNT  the loop counter         45 SKP   "emit this entry?"
31 SKQ   src_state, then "mTag=0" 37 SKT / 38 SKV  the option (tag, val), 2×
47 SAX   transient                22 SIX   readItem's index (LT_B; no ltCheck here)
15/16/26  CliqueRelTM.readNum's reserved HEAD/INBLK/SKIPR
```
`probes/S1StepEmitProbe.lean` §2 measures the entry body's write set as exactly
`SD1 ∪ {EOUT_C}`; `S1Step.LD` is the loop's, and `S1Program.LD_cdirty` proves it
sits inside the licence. **`SD1` doubles as the preamble's scratch** — `stepEmit`
clobbers it anyway, which is what makes the 30 registers suffice.

⚠ What no part of `stepBlocks` may touch: anything outside `CDirty` — the input
layout `1`–`5`, `PSIG`/`PSTATES`/`PSTART`/`PHALT`/`PNTRANS`/`PTRANS`, and
`EOUT_S`/`EOUT_I`.

## Composed-chain layouts — PINNED

* **chain head** (`Reductions/HeadLayout.lean`, frozen 2026-07-18):
  `headEncodeIn (M,s,maxSize,steps) = [[], encSyms (flattenTM M), encSyms s,
  1^maxSize, 1^steps]`, `headRegBound = 5`. C8-5's `mfc` keeps `0`–`4` and
  erases `[5,57)`.
* **S1 exit = tail entry**: `FlatTCCFree.encodeIn C = [] :: S1Program.s1Key C`
  (6 registers). The fourth seam's `mfc` keeps `1`–`5`, erases `0` and
  `[6,48)`; `[48,57)` closes by `Cmd.eval_length_le`.
* **tail exit** (`regBound = 57`): reg 1 = `1^|N|`, reg 2 = `encodeCnf N` (the
  SAT verifier's `CLAUSE_TALLY`/`CNF_STREAM` layout; `decodeOut = invFun
  encodeCnf` on reg 2), reg 0 = `serF f`, `buildSAT` scratch 3–26 dirty,
  27–56 hold the left composite's residue, `≥ 57` read `[]`.

## The free line — the working architecture (use this, and only this)

- **Verifiers**: free `DecidesLang` with bespoke bit-level `encodeIn`
  (numbers UNARY) → `DecidesLang.toDecidesBy`/`toInTimePoly` (live:
  `evalCnfDecidesLang`, `cliqueRelDecidesLang`).
- **NP witnesses**: `InNPWitnessLangFree`/`inNPLangFree` (+ `inNPLangFree_to_inNP`);
  hardness is quantified over `InNPWitnessLangFreeSplit` (`NPhard''`).
- **Reductions**: free `PolyTimeComputableLang` → `toFrameworkWitness'`/
  `reducesPolyMO'_of_langFree`; verifier precomposition via
  `DecidesLang.FreePrecomposeData`/`red_inNP_of_langFree`; **witness-witness
  composition via `SeamData`/`comp` — LIVE FIVE TIMES**
  (`FlatTCCBinComp.flatTCC_to_binaryCC_seam` →
  `BinaryCCFSATComp.binaryCC_to_FSAT_seam` → `FSATSATComp.fsat_to_SAT_seam` →
  `S1SATComp.s1_to_SAT_seam` → `FrontS1Comp.front_to_SAT_seam`).
  Four seam shapes exist; pick the one that matches:
  - **wider right frame** → length argument (`BinaryCC_to_FSAT_comp.lean`);
  - **narrower right frame** → no scrub above it (`FSAT_to_SAT_comp.lean`);
  - **left is a composite** → stacked seam, unfold its `.c` with one `heval`
    and push the previous bridge through with `Cmd.eval_agree`
    (`BinaryCC_to_FSAT_comp.lean`);
  - **right is a composite** (preferred at the head of the chain — FINDING A)
    → nothing to unfold, just scrub to the composite's frame
    (`Front_to_S1_comp.lean`).
- **Templates for new reduction witnesses** — copy these, not first principles:
  - `NP/kSAT_to_SAT_free.lean`: re-encoder + reduction sharing one program,
    fold invariants, tight `encodeIn_size`, `FreePrecomposeData`.
  - `Reductions/FlatTCC_to_FlatCC_free.lean`: the unguarded-map pattern
    (backward validity transfer + unconditional iff), shared-layout registers,
    `blockMove`/`halfMove` stream re-formatting, `encSList` prefix-free
    injectivity, multi-field decode via `Function.invFun encKey`.
  - `Reductions/FlatCC_to_BinaryCC_free.lean`: **the guarded-map pattern** —
    on-machine validity flag (`allLtB` reflection ↔ `isValidFlattening` via
    `validB_iff`), guard branch to the no-instance, the item view of sentinel
    streams (`encItems`/`expandItems` — ONE loop lemma for cards+final via a
    shared scratch output `BOUT` + copy-out), unary multiplication
    (`mulLoop_run`), truncated-subtraction compare.
  - `Reductions/FSAT_to_SAT_free.lean` + `NP/FSAT_to_SAT_pre.lean`: **the
    tree-traversal pattern** — a TREE-typed *input* consumed by one forward
    token scan of its Polish serialization: positional fresh variables, right-
    child recovery by the arity-budget scan (`subtreeScan`), and a pure scan
    model proven equal to the tree map (`mScan_eq_fsatToSat`) — the template
    for "prove the machine folds compute a pure model, then close with the
    model≡tree equivalence".
  - `Reductions/S1_to_FlatTCC_comp.lean`: **the scrub-only seam** —
    `clearRange` + one `_get` clause + a bridge quantified over the left
    program's contracts. **Start here for any new seam.**
- **The canonical `LangEncodable` layer stays DEAD** (generic product encoding
  is size-unsound — `probes/UnaryProductSizeProbe.lean`). Do not rebuild it.

### ⚠ Standing architecture risks — check every new witness against these

1. **Honesty is per-witness discipline, not enforced.** `eIn`/`encodeIn` must
   be the natural layout of the *input* (never of `gmap v`), `decodeOut` the
   inverse of the natural *output* layout, all reduction work in the `Cmd`.
   The trivial dishonest instantiation satisfies every field — review each
   witness. **The end-to-end audit is NEXT-TOP-DOWN item 3 and is not done.**
2. **Seam discipline**: pin each new witness's input layout to its
   predecessor's exit frame and document the exit layout (dirty registers
   included) for the successor. See "Composed-chain layouts — PINNED" above;
   changing any of them re-opens a bridge.
3. **Guard-or-no-guard is a per-step decision**: probe invalid→invalid ON
   PAPER before coding (counterexample method: pick a tiny invalid instance,
   check whether its image is accidentally wellformed+satisfiable).
4. **The front instance types are size-MEASURED, not string-encodable**:
   `GenNPInput.rel` / `mTMGenNPFixedInput.accepts` / `TMGenNPFixedInput.accepts`
   are abstract predicates, so `encodable.size` counts only the data fields.
   Honest for `⪯p` size bounds, but **no TM can consume these types as
   inputs** — C8 retires the abstract front entirely. Never add a size-0
   instance to "fix" a missing-instance error; the fallback was deleted
   deliberately.
5. **`encodable.size` must DOMINATE the register content, not merely count the
   structure.** A size that counts a container's *elements* but not their
   *payloads* is honest for `⪯p` output-size bounds yet makes `encodeIn_size`
   unsatisfiable for any witness that must spell the value out on tape — that
   is what killed `sizeFlatTM`. For every new type ask: *does some witness have
   to write this structure out cell by cell?* If yes, the size must be the
   data-field sum.
6. **The hypothesis side of hardness is dishonest-capable too.**
   `inTimePoly`/`inNP` are classically TRUE for every predicate (the cheating
   `DecidesBy.encode`), so any `∀ Q, inNP Q → …` hardness statement is
   unprovable-honestly by construction. Quantify hardness over free-line
   verifier witnesses (`NPhard''` over `InNPWitnessLangFreeSplit`) and never
   "fix" a hardness obligation by strengthening only the conclusion side. Do
   **not** close `hasDeciderClassical` with the cheating encoder.
7. **A `sorry` inside a `def` poisons the STATEMENT of every lemma mentioning
   it**, which blinds `#print axioms` — the project's main soundness
   instrument. **Quantify skeleton-phase results over the placeholder.** This
   is why `s1Bridge` takes the program as a parameter and why
   `SAT_NPhard''_of_S1` exists; it is the single most valuable habit in this
   codebase and it is what turns "we believe S1 is the only gap" into a
   machine-checked fact.

## C8 — the honest universal front: DONE (C8-0…C8-5)

The per-`Q` front and its seam into the chain are built and the front half is
axiom-clean. Consume as black boxes; do NOT re-derive the machine, the lifting,
the program or the seam:

* `Complexity.Lang.FrontWitness.front_reducesPolyMO' : Q ⪯p' FlatSingleTMGenNP`,
  the witness `WQ`, and `FrontLifting.fQ_correct` / `fQ_correct_concrete`;
* `FrontS1Comp.frontBridge` / `front_to_SAT_seam` / `SAT_NPhard''_of_S1`.

## ★ Earlier findings that still bind

Narration lives in git history; the durable results are in "Proven, reusable",
"Locked invariants" and "Conventions". These are the *findings* a new gadget
still has to respect:

- `preludeBlocks` is ~96% of the card register, so the prelude is stage C's
  cost driver; `cFive`'s five families all emit IDENTITY cards and `stepBlocks`
  does **not** — `S1Step.emitCard`/`card6_run` (six pairs of registers) is the
  atom for any future non-identity card family.
- `Cmd.op (.copy r r)` is the layer's no-op (`S1CardEmit.copy_self_get`);
  `forBnd` samples its bound register's length ONCE at entry; `ifBit` reads its
  test register *before* entering the branch (which is why `CDirty` includes
  `FLG = 17`).
- `xv` is rebuilt per iteration while `hv` is carried — ask which shape a new
  value register is.
- Stages P/G/F take **no** validity hypothesis (the parse never desynchronises;
  a drained-empty `head` reads *false*, exactly `M.halt.getD` out of range) —
  but **the guard is load-bearing** for stage I (`probes/S1EmitProbe.lean`
  exhibits an off-guard instance where stage I and `preludeRow` disagree).
- `PHALT` (reg 11) is a RAW BIT LIST; registers `15`/`16`/`22`/`26` are
  RESERVED for `CliqueRelTM.readNum`/`ltBit`.
- Both S1 size bounds are `≤ (2·(b+1))^10` and the **enlarged base is not
  optional**: a `C·b^d` collapse overshoots a tight `n^10` at small `n`, and
  guess's base includes `maxSize`.
- `W_Q.encodeIn x := encX x ++ [1^(size x)]` carries a unary size register
  because the `tallyCells` monomial argument cannot discharge `fQ_correct`'s
  `hmax`/`hsteps`; C8-5's `mfc` drops it. `tallyCells` is UNUSED.
- The S1 v2 redesign's two machine-checked defects — non-local zero-padding
  jump-writes and the **phantom head** at the right row edge — are why the tape
  is append-only at the frontier and why `confRow` carries a right boundary
  marker. Both are locked invariants below.

---

## Locked invariants — do NOT revisit

- **A cost predicate with ONE cap cannot survive a loop (2026-07-29,
  FINDING Z).** `Cmd.PolyCost`'s single `M` over `costReads` re-caps the body's
  outputs at `poly(M)` each iteration, so `m` iterations give a tower; that is
  why `Cmd.polyCost_forBnd` has to forbid the body from writing what it
  cost-reads. `Cmd.CapCost` splits the cap into a frozen `MF` and a global `N`,
  lets the **cost** be linear in `N` and forbids the **growth** from depending
  on it. Do not "simplify" it back to one cap.
- **`Cmd.GrowOk`'s frozen set must be UNWRITTEN by the command (2026-07-29).**
  `Cmd.growOk_sound`'s `seq` case re-establishes the cap with
  `Cmd.eval_get_of_not_writes`. So promoted (hence written) registers may **not**
  be fed back into `GrowOk`, and iterating `Cmd.promote` to a fixpoint is
  unsound. The one safe widening is `NoGrow` members, whose bound
  (`≤ max |r| 1`) survives a `seq`. Reaching `SSEEN` needs a *merged*
  flow-sensitive pass, not more rounds.
- **`Cmd.op (.copy r r)` costs `|r| + 1` and that is now FREE (2026-07-29).**
  FINDING X (2026-07-28-c) still describes the program correctly — the `ifBit`
  else-branch no-op on `EOUT_C` makes the emitters `O(output²)` — but
  `Cmd.CapCost`'s `(N+1)` factor pays for it. **Do not swap the no-op**; the
  pinned `_run` lemmas depend on that exact else-branch and there is no longer
  any cost reason to touch it.

- **A `cost_bound` field must be an EXISTENTIAL polynomial, not a fixed one
  (2026-07-28-c, FINDING Y).** `S1Witness.S1CostBound c` = "some `cb` is
  `inOPoly`, `monotonic`, and dominates both `c.cost (headEncodeIn x)` and
  `size (s1Map x)`". The old `c.cost ≤ S1Map.s1Bound` (degree 10, fixed) could
  not consume any generic cost lemma, whose output is always `∃ K D, K·(M+1)^D`.
  `output_size_le` is the *only* real constraint on `cost_bound`, which is why
  bundling the two obligations makes the bound free. Do not re-specialise it.
- **`Cmd.op (.copy r r)` is a semantic no-op but costs `|r| + 1`
  (2026-07-28-c, FINDING X).** It is used as the `ifBit` else-branch with
  `r := EOUT_C` in `S1CardEmit`, `S1Prelude` and `S1PreludeEmit`, so the
  emitters are `O(output²)` and `EOUT_C` is a genuine `Cmd.costReads` member.
  The program stays polynomial and the pinned `_run` lemmas depend on that exact
  else-branch — **do not swap it**. For a NEW gadget, prefer a `clear` on a
  scratch register already in the frame's dirty list.
- **No unconditional polynomial cost bound exists for `Cmd`
  (2026-07-28-c).** `forBnd cnt bnd (concat dst dst dst)` squares `dst` every
  iteration. Every cost lemma therefore carries a side condition; `CostSafe`'s
  is "no loop body writes a register its own cost reads". Relax it, never drop
  it — and remember the loop *bound* register is sampled once at entry, so it
  may be written by the body without harm, but an inner loop bounded by a
  register the outer body rebuilds is exactly where compounding sneaks back in.

- **A cursor loop's body must be TOTAL (2026-07-28-b, FINDING T).**
  `S1Step.emitFold_run`'s `hstep` is quantified over every iteration index, so
  the body has to emit `[]` and preserve the carried state on an exhausted
  cursor. Guard every cursor loop's body with one `nonEmpty` on its own cursor
  (`S1Step.entryBody`, `scanBody`); a guarded loop then only needs an **upper**
  bound on its iteration count (FINDING V — `Cmd.forBnd EK1 SSEEN scanBody` is
  legitimate because `|encSyms (keyFlat seen)| ≥ |seen|`). Do not spend a
  register on an exact loop count.
- **A machine-side accumulator must match its model's cons order
  (2026-07-28-b, FINDING U).** `S1Step.stepSt` conses, so the seen register is
  built by `Cmd.op (.concat SSEEN item SSEEN)` — `concat dst a b` writes
  `get a ++ get b`, so prepending is free and keeps the invariant a literal
  `encSyms (keyFlat seen)`.
- **A contract pinned for an unwritten `Cmd` must list the inputs of every
  model it will consume (2026-07-28-b, FINDING W).** `stageC_run` was pinned
  without `PSTART` and nothing noticed for three sessions, because no *built*
  consumer needed it yet — `S1Cards.preludeBlocks` is indexed by
  `min M.start M.states`. The fix was free here; it will not always be.
- **Stage C's `Cmd` is COMPLETE and its 30-register licence is EXACTLY full
  (2026-07-28-b).** `S1Program.stageC = cFive ;; S1Step.stepFam ;;
  S1Prelude.cPrelude`, emission order is `S1Cards.cardBlocks`' order, and
  `probes/S1StepLoopProbe.lean` §1 checks the full equality (not a prefix).
  Changing any register in the stage-C table re-opens `stepFam_run`,
  `cPrelude_run` and `stageC_run`.

- **A data-driven loop needs a STATEFUL loop principle (2026-07-28, FINDING R).**
  `S1CardEmit.emitLoop_run` pins the body's output to the iteration index and is
  correct only for *index-driven* loops (the five copy/halt families, the whole
  prelude nest). A loop whose output depends on registers inside its own dirty
  set — a cursor, an accumulator — must go through **`S1Step.emitFold_run`**
  (`Cmd.foldlState_range_induct` + an invariant carrying an abstract state).
  Do not try to force a cursor loop into `emitLoop_run`.
- **Parameterise a family gadget by its innermost BODY, not by its branch
  condition (2026-07-28, FINDING Q).** `stepBlocks` branches three ways on `mv`
  and has four sub-families; because the four *loop nests* are `mv`-independent,
  taking the card `Cmd` as a parameter turned 12 emitters into 4 loop lemmas +
  11 card definitions. `S1Prelude.pKindCmd` and `S1CardEmit.haltFam` are the
  same move.
- **The `stepBlocks` entry body is BUILT; its contract `SConst`/`SEntry`/`SD1`
  is PINNED (2026-07-28).** Changing any register in the table above re-opens
  `stepEmit_run` and all four family `_run`s. The entry loop must meet
  `S1Step.stepSummand_fold`; the dedup's seen-set is appended to
  **unconditionally** (FINDING S, `dedupK_congr`).
- **The prelude family is BUILT; its emission order and register table are
  PINNED (2026-07-27-b/-c).** `S1Prelude.preludeSeg`/`preludeSeg'` fix the
  nesting (kind loops outside resolution loops — finding A) and `cPrelude` is
  the emitter. Changing either re-opens `preludeBlocks_seg`,
  `preludeBlocks_seg'`, `pPre_run`, `cPrelude_run` and `S1Program.cFive_frame`.
- **Stage C needs NO unary comparison gadget — BOTH families (2026-07-27-b/-c).**
  The seven-segment split (`S1Prelude.range_seg`) makes every prelude kind's
  shape a compile-time constant; `S1Step.range_last`/`range_first_last` do the
  same for `stepBlocks`' three last-iteration tests; `S1Prelude.minReg` does
  every `min` by draining and `S1CardEmit.loadX` does every "is the counter
  zero?" with `nonEmpty`. Do not build a `<`/`=`-on-unary gadget for stage C.
- **A register may not be shared by two writers separated by a loop
  (2026-07-27-c, FINDING G).** The pinned table gave `PJᵢ` to both the kind
  level and the resolution level; because the resolution nest runs inside the
  kind levels, the kind level's value never survived to the emit body. Fold the
  extra value into an existing register (`PPAᵢ := 1^pav`) instead of making the
  frame conditional. Applies to every future multi-level emitter.
- **A deep register-generic nest needs NESTED dirty lists (2026-07-27-c,
  FINDING H).** `DK3 ⊆ DK2 ⊆ DK1` and `DR3 ⊆ DR2 ⊆ DR1`: level `i`'s frame must
  not claim level `i-1`'s registers, because the innermost body reads them. One
  global dirty list does not work. `S1Prelude.Emits.mono` is the bridge.
- **The chain composes RIGHT-NESTED: `W_Q ⨾ (S1 ⨾ tail)` (2026-07-27).**
  `S1SATComp.s1_to_SAT_witness` first, `FrontS1Comp.front_to_SAT_witness` on
  top. Re-associating turns C8-5 into a stacked seam over a composite left
  witness and re-opens `frontBridge`.
- **The two new scrub ranges are PINNED to the frames they were derived from
  (2026-07-27).** `S1SATComp.scrub4` erases `{0} ∪ [6, s1RegBound)`;
  `FrontS1Comp.headScrub` erases `[headRegBound, 57)`. `probes/SeamS1Probe.lean`
  §1 asserts both erase sets exactly. Changing `s1RegBound`, `headRegBound` or
  the tail composite's `57` means changing a scrub and re-running that probe.
- **The S1 witness is built in TWO steps and stays that way (2026-07-27).**
  `S1Witness.s1WitnessOf` takes the program + its three contracts;
  `s1_reductionLang` is the instantiation. Both seams, both composites and
  `SAT_NPhard''_of_S1` are stated over the parameterised form, which is what
  keeps them axiom-clean while stage C is a placeholder. Inlining
  `s1WitnessOf` would silently destroy that (standing risk #7).
- **The S1 program's SHAPE and `stageC_run` are PINNED (2026-07-26-b/-c,
  `Reductions/S1Program.lean`)**: `s1Program = stagePG ;; ifBit FLG yesBranch
  stageMNo`, `yesBranch = Σ ;; I ;; C ;; F ;; M-yes`, and `stageC_run` states
  exactly what the assembly consumes. `s1Program_computes` is already the
  witness's `computes` field. Changing the stage order, the contract, or the
  `EScratch`/`CDirty` licences re-opens `yesBranch_run` and hence `computes`.
- **The S1 register frame is PINNED across three files** — see "The S1 register
  frame — PINNED" above for the single authoritative table (`S1Parse` `0`–`31`,
  `S1Emit` `32`–`47`, `S1CardEmit`'s constants inside `[14,32)`,
  `s1RegBound = 48`; registers `15`, `16`, `22`, `26` RESERVED for
  `CliqueRelTM.readNum`/`ltBit`). Changing any of it re-opens `stagePG_usesBelow`,
  `stagePG_frame`, all four emitter `_run`s and every `usesBelow`.
- **Stage C emits in `cardBlocks` ORDER (2026-07-26-c).** `S1CardEmit.cFive` is
  the first five summands and `probes/S1CardEmitProbe.lean` §1 asserts its
  output is a genuine PREFIX of `encNats (cardBlocks M)`. The remaining two
  families append after it, `stepBlocks` then `preludeBlocks` — build order is
  free, emission order is not.
- **The emitter's dirty sets are register LISTS (2026-07-26-c).**
  `S1CardEmit.HD`/`ID`/`AD` with `r ∉ D` (`by decide`), plus `nmem_sub` /
  `ne_of_nmem` to move between levels and down to a per-gadget `≠`. An 11-`≠`
  frame chain is a smell; `S1Program.cFive_frame` is what proves a list-shaped
  dirty set fits the coarse `CDirty` predicate.
- **`s1Key`/`s1Extract`/`SIGMA`…`STEPS`/`s1RegBound` live in `S1Program`, not
  `S1Witness` (2026-07-26-b).** The witness imports the program. Do not move
  them back or duplicate them.
- **A skeleton-phase lemma must quantify over the placeholder it does not depend
  on (2026-07-26-b).** A `sorry` inside a `def` puts `sorryAx` in the axiom list
  of *every* lemma whose statement mentions it, proof or no proof — which blinds
  `#print axioms`, the project's main soundness instrument. `noBranch_computes`
  takes `(yes : Cmd)` and is axiom-clean; `s1Program_computes_neg` is its
  corollary and is not. State the general form first, specialise second.
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

- **`Complexity/Lang/CostPoly.lean` — the cost-ladder toolkit (2026-07-28-c).**
  `Cmd.PolyCost` (+ `.seq`, `.ifBit`, `polyCost_op`, `polyCost_forBnd`),
  `Cmd.CostSafe` + `polyCost_of_costSafe` (one `decide` per gadget),
  `polyCost_forBnd_grow` / `polyCost_tailLoop` / `polyCost_mulLoop`,
  `Cmd.get_length_eval_le` (per-register growth ≤ cost) and
  `PolyCost.cost_le_size`. Sits on top of `Lang/CostFlat.lean`
  (`cost_le_flat`, `cost_forBnd_flat_le`, `cost_mulLoop_le`,
  `cost_tailLoop_le`, `Cmd.writes`, `Cmd.costReads`). **Start every new
  `cost_le` obligation here, not with `Cmd.cost_seq` chains.**

- **Stage C's `stepBlocks` family — THE PREAMBLE AND THE LOOP (2026-07-28-b,
  `Reductions/S1StepLoop.lean`, sorry-free & axiom-clean — consume as black
  boxes; do NOT re-derive a cursor walk, a scan or the loop's invariant)**: the
  endpoints **`stepFam`/`stepFam_run`/`stepFam_usesBelow`** (the whole family:
  `Emits LD stepFam ((normTrans M).flatMap (entryBlocks M)) s`) and
  **`entryPre`/`entryPre_run`/`entryPre_usesBelow`** with its four phases
  `preSrc`/`preKey`/`preDst`/`preMv` (+ `_run`); the loop layer
  **`entryBody`/`entryBody_run`… (`entryBody_step`, `LInv`, `LInv_set`,
  `entryBody_usesBelow`)** and **`Emits.pre_op`**; the register frame
  `SCUR`/`SSEEN`/`SCNT`/`SKP`/`SKQ`/`SKT`/`SKV`/`SAX`/`SIX`, the dirty list
  **`LD`** (+ `SD1_LD`, `S1Program.LD_cdirty`) and the frame workhorse
  **`Keeps`/`Keeps.seq`/`keeps_of_writes`** (a command whose syntactic write set
  is inside `LD` preserves everything outside it — `by decide` at every use);
  the seen-set model **`keyFlat`/`keyFlat_cons`/`keyFlat_len_le`** and
  **`seenHit`/`seenHit_snoc`**; and the **general-purpose gadgets**:
  **`dropLoop`/`dropLoop_run`** (random access into a raw list),
  **`haltBlk`/`haltBlk_run`** + `head_drop_iff` (the `PHALT` lookup),
  **`optRead`/`optRead_run`** (one `encOptN` group off a cursor),
  **`hvBlk`/`hvBlk_run`** (`1^(hv σ (min q states) 0)` = `minReg` + one hoisted
  `unaryMulLoop`), **`optMin`/`optMin_run`** (`rOf`/`wOf`'s shared shape),
  **`wBlk1`/`wBlk1_run`**, **`mzBlk`/`mvBlk`** (+ `_run`),
  **`scanSeen`/`scanSeen_run`** (+ `scanBody`, `SInv`) and
  **`pushKey`/`pushKey_run`**; plus `lnop`/`lnop_get` (the no-op *inside* `LD`;
  `snop` writes `EOUT_C`), `snop`/`snop_get`, `keep_and`, `flattenEntry_shape`,
  `wOf_false_eq`/`wOf_true_eq`.
  In `S1Program.lean`: **`stageC`/`stageC_run`/`stageC_usesBelow`** (closed) and
  `LD_cdirty`. Probe: `probes/S1StepLoopProbe.lean`.

- **Stage C's `stepBlocks` family — THE ENTRY BODY (2026-07-28,
  `Reductions/S1StepEmit.lean`, sorry-free & axiom-clean — consume as black
  boxes; do NOT re-derive a card, a loop nest or the `mv` split)**: the endpoint
  **`stepEmit`/`stepEmit_run`/`stepEmit_usesBelow`** and the frames
  `SConst`/`SEntry`/`SConst_frame`/`SEntry_frame`/`SFr`/`SD1`/`SD2`/`SD3`;
  **`SConst_of_cFive`** (+ `S1CardEmit.cFive_const`, also new — the machine
  constants survive `cFive`, so the preamble owes only `SEntry`); the card atom
  **`emitCard`** + `card_run` + **`card6_run`** and the eleven card lists
  `cardCN`/`cardCR`/`cardCL`/`cardLN`/`cardLR`/`cardLL`/`cardRN`/`cardRR`/
  `cardRL`/`cardIR`/`cardIL` (+ `_run`, `_usesBelow`); the four loop nests
  **`cenFam`/`lefFam`/`rigFam`/`inFamR`/`inFamL`** (+ `_run`, `_usesBelow`),
  register-generic in their card `Cmd`s; the three arms `bodyN`/`bodyR`/`bodyL`
  (+ `_run`, `_usesBelow`); **`loopFr`** (`emitLoop_run` in `Emits` shape),
  `loadX_emits`, `EmitsFr_congr`, `Emits_of_eval`, `hv_split`.
  **The entry loop's layer**: **`emitFold_run`** (the stateful loop principle —
  project-wide utility), `dedupK_congr`, **`stepGo`** + `stepGo_eq` +
  **`stepSummand_go`**, and `stepSt`/`stepOut`/`stepGo_iter`/
  **`stepSummand_fold`** (the loop's target in `emitFold_run`'s shape).
  Probe: `probes/S1StepEmitProbe.lean`.
- **Stage C's prelude family — THE `Cmd` (2026-07-27-c,
  `Reductions/S1PreludeEmit.lean`, sorry-free & axiom-clean — consume as black
  boxes; do NOT re-derive an emitter nest)**: the family
  **`cPrelude`/`cPrelude_run`/`cPrelude_usesBelow`** and `PDirty`/
  **`PDirty_cdirty`**; the emitter contract **`Emits`** (dirty-list-indexed
  "appends `encNats l` to `EOUT_C`") + `Emits.seq`/`.mono`/`.nop`/`.congr_l`
  and **`EmitsFr`** (the same from any state agreeing outside `D`) +
  `EmitsFr.seq`/`.here` — **use these for `stepBlocks` too**; the
  register-generic gadgets **`pRes`/`pRes_run`** (one resolution level),
  **`pSeg`/`pSeg_run`** (publish unary values, then continue) and
  **`pKindCmd`/`pKindCmd_run`** (one kind level = seven segments), each proven
  once and applied three times; the assemblies `resNest`/`resNest_run`,
  `kindNest`/`kindNest_run`, `pEmit`/`pEmit_run` and every `_usesBelow`; the
  value gadgets **`setLit`/`loadSum`/`loadVal`/`setFlag`** + `sumLen`/
  `sumLen_congr` and the flag codec **`flagRep`**/`setTrue`; and the
  re-coordinatised model `pResLevel'`/`pKindSeg`/`pKindSeg_of`/`pKindSeg_eq`/
  `preludeSeg'` + **`preludeBlocks_seg'`**.
  Probe: `probes/S1PreludeEmitProbe.lean` (⚠ ~6 min).
- **`stepBlocks`'s emitter-shaped model (2026-07-27-c,
  `Reductions/S1StepModel.lean`, sorry-free & axiom-clean — build the `Cmd`
  against these, do NOT re-derive a segment split)**: the range splits
  **`range_last`** (`range (n+1) = range n ++ [n]`) and **`range_first_last`**
  (`range (σ+2) = [0] ++ (range σ).map (·+1) ++ [σ+1]`); the per-card cells
  `cCard`/`lCard`/`rCard` (each keeps `mv` as a parameter so one `_run` lemma
  serves all three `mv` arms); the four family reformulations
  `stepCenterSeg`/`stepLeftSeg`/`stepRightSeg` + `stepCenterBlocks_seg`/
  `stepLeftBlocks_seg`/`stepRightBlocks_seg`; and the endpoints **`stepSeg`** +
  **`stepBlocks_seg`**, `entrySeg` + `entryBlocks_seg`, and
  **`stepSummand_seg`** (`(normTrans M).flatMap (entryBlocks M) =
  (normModel M).flatMap (entrySeg M)`, the target the entry loop must meet).
  Probe: `probes/S1StepModelProbe.lean`.

- **Stage C's prelude family — model + preamble + two general atoms
  (2026-07-27-b, `Reductions/S1Prelude.lean`, sorry-free & axiom-clean —
  consume as black boxes)**: the emitter-shaped target
  **`preludeSeg`** + **`preludeBlocks_seg`**, built from `range_seg`,
  `resShape`/`resOf_special`/`resOf_tapeBand`/`resOf_headBand`, `pGate` +
  `contigB_prop` + **`pBody_gate`**, and `pResLevel` + `pGate_resShape` +
  `pKindLevel` + `pKindLevel_eq`; the two general atoms **`emitList`** +
  `emitList_run` (a run of `emitBlk2`s over a list of source pairs — use this,
  not `emitId`, for any family emitting six different values) and **`minReg`** +
  `minReg_run` (`1^(min a b)` by draining, no comparison gadget); and the
  preamble **`pPre`** + `pPre_run` + `pPre_usesBelow` establishing `PConst`
  (`ESG`, `PBV`, `PZ`, `PB5`, `PHB = 1^(hv σ q0 0)`). Register table `PBV`…`PFL`
  + `PD`/`PAll` + `prelude_regs_cdirty`. Probe: `probes/S1PreludeProbe.lean`.
- **The two head seams and the parameterised endpoint (2026-07-27,
  `Reductions/S1_to_FlatTCC_comp.lean` + `Reductions/Front_to_S1_comp.lean`,
  both sorry-free; the `…Of` / `…_of_S1` forms are AXIOM-CLEAN — consume as
  black boxes, do NOT re-derive a scrub or a bridge)**: the generic scrub
  gadget **`S1SATComp.clearRange`** + `clearRange_get` / `clearRange_cost`
  (`≤ 2n+1`) / `clearRange_usesBelow` and the frame closer
  `get_nil_of_len_le`; **`scrub4`** + `scrub4_get`/`_cost`/`_usesBelow` and
  **`headScrub`** + `headScrub_get`/`_cost`/`_usesBelow`; the layout facts
  `headEncodeIn_length` / `flatTCC_encodeIn_length` /
  `FrontS1Comp.headEncodeIn_eq` and the five `rfl` projections
  `FrontS1Comp.get5_0`…`get5_4`; the two bridges **`S1SATComp.s1Bridge`**
  (over an arbitrary S1 program) and **`FrontS1Comp.frontBridge`**; the seams
  `s1_to_SAT_seamOf`/`s1_to_SAT_seam` and
  `front_to_SAT_seamOf`/`front_to_SAT_seam`; the composites
  `s1_to_SAT_witnessOf`/`s1_to_SAT_witness` (+ the frame equation
  `s1_to_SAT_witnessOf_regBound = 57`) and
  `front_to_SAT_witnessOf`/`front_to_SAT_witness`; the chained correctness iff
  **`s1_to_SAT_correct`**; and the endpoints
  `s1_to_SAT_reducesPolyMO'_of`/`s1_to_SAT_reducesPolyMO'`,
  `front_to_SAT_reducesPolyMO'_of`/`front_to_SAT_reducesPolyMO'`,
  **`SAT_NPhard''_of_S1`** (axiom-clean) / `SAT_NPhard''`.
  In `S1Witness.lean`: **`s1WitnessOf`** and the **only remaining open S1
  obligation**, the cost ladder `s1Program_cost_le`. Probe: `probes/SeamS1Probe.lean`.

- **Stage C's copy/halt families and the emitter loop principle (2026-07-26-c,
  `Reductions/S1CardEmit.lean`, sorry-free & axiom-clean — consume as black
  boxes; do NOT re-derive a loop invariant or an append gadget)**: the loop
  principle **`emitLoop_run`** (register-generic, dirty set as a `List Var`) and
  its two frame helpers `nmem_sub` / `ne_of_nmem`; the atoms **`emitBlk2`** +
  `emitBlk2_run` (`encNat (|src1|+|src2|)`) and **`emitId`** + `emitId_run`
  (the identity card `p₁ p₂ p₃ p₁ p₂ p₃`); `encNats_nil`; **`copy_self_get`**
  (the layer's no-op `Cmd.op (.copy r r)`); the register frame
  `CBV`/`CS1`/`CS2`/`CQ1`/`CX`/`CH`/`CD`/`CE`/`CZ` and the dirty lists
  `HD`/`ID`/`AD`; the constants bundle **`CConst`** + `CConst_frame`;
  **`loadX`/`loadX_run`** (`1^(xv sig states x)` off a loop counter);
  **`haltBody`/`haltFam`/`haltFam_run`** (the gated `q` loop with the carried
  head-cell base and the `PHALT` drain — the shape all three halt families
  share); the five families **`cCopy`/`cRight`/`cHaltLeft`/`cHaltCenter`/
  `cHaltRight`** + `_run`; the preamble **`cPre`/`cPre_run`/`cPre_usesBelow`**;
  and the assembly **`cFive`/`cFive_run`/`cFive_usesBelow`** (48).
  In `S1Program.lean`: **`stageMYes`/`stageMYes_run`/`stageMYes_usesBelow`**
  (closed) and the risk checks **`mem_AD_cases`/`cFive_frame`/`cFive_preserves`**
  (the built families' dirty set sits inside `CDirty`, and they preserve
  registers `1`–`5`, `PSIG`/`PSTATES`/`PHALT`/`PNTRANS`/`PTRANS`,
  `EOUT_S`/`EOUT_I`). Probe: `probes/S1CardEmitProbe.lean`.
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
  **`s1Program_usesBelow`**. **Nothing is open in this file any more** —
  `stageC` landed 2026-07-28-b and `s1Program_computes`/`s1Program_usesBelow`
  are axiom-clean. Probes: `probes/S1ProgramProbe.lean`,
  `probes/S1CardEmitProbe.lean`, `probes/S1StepLoopProbe.lean`.
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
  (`≤ 8·n + 4`); the parameterised witness **`s1WitnessOf`** and its
  instantiation **`s1_reductionLang`**, every mechanical field discharged.
  **OPEN in this file: `s1Program_cost_le` only.**
  (`s1Key`/`s1Extract`/`SIGMA`…`STEPS`/`s1RegBound` live in `S1Program`.)
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
  bit-level). Probe `probes/C8ProgramProbe.lean`; `emitRegs_cost` and
  `frontProgram_cost_le` landed 2026-07-24-b.
- **The C8-4 witness `WQ` + endpoint reduction (2026-07-24,
  `Reductions/FrontWitness.lean`, all axiom-clean; consume verbatim)**: **`front_reducesPolyMO' : Q ⪯p' FlatSingleTMGenNP`** (the
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
- **NEW (2026-07-27): `omega` is blind to `Var`-typed HYPOTHESES, not only
  goals.** `h : (lo : Var) + 1 ≤ r` is simply not collected ("No usable
  constraints"), and `have := h.1` does not help. Scalable fix: **declare
  register parameters as `Nat`** — `Var` is an `abbrev` for it, so
  `Cmd.op (.clear lo)` accepts either, and every `omega` inside then just works
  (`S1SATComp.clearRange` and all its lemmas are stated this way).
- **NEW (2026-07-27): never let `exact`/`rfl` unify a value against
  `State.get <layout applied to a big constant> k`.** The unifier starts
  *evaluating* the constant (`flattenTM (MQ …)` — a whole compiled machine) and
  burns a 1M-heartbeat budget. Rewrite the layout to a literal list first
  (one `rfl` equation on opaque components) and read registers with `rfl`
  projections (`FrontS1Comp.get5_0`…`get5_4`).
- **NEW (2026-07-27): `by decide` cannot run on a goal that still mentions a
  parameter** ("Expected type must not contain free variables"). Once a witness
  is parameterised over its program, its `regBound` has free variables. State
  the frame as an **equation** (`… .regBound = 57`, by `rfl`) and `rw` it first.
- **NEW (2026-07-27): `variable (…)` does NOT give a family of declarations the
  same signature** — Lean includes only the variables each declaration
  *mentions*, so a theorem whose statement does not mention the parameters
  silently loses them and starts auto-binding. Spell the binders out on each
  declaration of a parameterised family.
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
- **NEW (2026-07-26-c): a frame clause should quantify over a register LIST, not
  a chain of `≠`s.** `∀ r, r ≠ dst → r ∉ D → …` composes: `nmem_sub (by decide)`
  widens/narrows `D` between loop levels and `ne_of_nmem h (by decide)` produces
  the per-gadget `r ≠ EK1` that an atom's `_run` wants. Both memberships are
  `by decide` at concrete registers. This is what kept five nested-loop families
  to ~40 lines of proof each.
- **NEW (2026-07-26-c): `refine <lemma> … (fun i t h1 h2 => ?_)` inside a `have`
  does not work** — `?_` is `refine`-only syntax. State the intermediate result
  as an explicit `have key : … := by refine …` and project afterwards.
- **NEW (2026-07-26-c): `rw` needs the loop body SYNTACTICALLY.** After
  `refine emitLoop_run … body …` the goal mentions the body's `def` name, while
  the atom's `_run` lemma is about its unfolded form — `unfold <bodyDef>` first
  (or close with `exact`, which is up to defeq; only `rw` is syntactic).
- **NEW (2026-07-26-c): a doc comment `/-- … -/` cannot precede `#eval`** in a
  probe (`unexpected token '#eval'; expected 'lemma'`) — use a module comment
  `/-! … -/`. And a `Prop`-valued `#eval` needs an explicit `decide`.
- **NEW (2026-07-26-c): `fin_cases h` is the way to case on `r ∈ [<literals>]`**;
  `rintro (rfl|…)` fails ("not a free variable") because list membership is not
  syntactically a nested `Or`.
- **NEW (2026-07-26-c): `Cmd.UsesBelow` of a program containing a `private`
  sub-`def` cannot be closed by `simp [<defs>]`** — the private bodies do not
  unfold. `unfold <program>; refine ⟨<sub-lemma>, ?_⟩; simp [<the rest>]`
  (`S1CardEmit.cPre_usesBelow` over `S1Emit.loadSg_usesBelow` is the model).
- Methodology: **skeleton-first; refine the highest-risk gap next; decompose
  `sorry`s, don't elaborate them; probe before committing engineering;
  `def`+`sorry` over `axiom` (count = 0); build green between commits.**
