import Complexity.Complexity.Deciders.EvalCnfTM
import Complexity.Lang.CostGrow

set_option autoImplicit false

/-! # `inNPLangFreeSplit SAT` — the membership half of `NPcomplete'' SAT`

This file supplies the **design** and all the **pure** content of
`InNPWitnessLangFreeSplit SAT`, the last piece between the axiom-clean
`FrontS1Comp.SAT_NPhard''` and the honest headline `NPcomplete'' SAT`.
Everything except **one register equation** is discharged here; that equation is
`DecodesAssgn certDecode` (below) and every result is quantified over it — so
`satSplitWitnessOf` / `SAT_inNPLangFreeSplit_of_decodesAssgn` are axiom-clean
statements of exactly what is left (standing risk #7: never let a `sorry`-backed
`def` into a statement).

## The design, and why the layout worry was a non-issue

`InNPWitnessLangFreeSplit` demands three things the live SAT verifier
(`EvalCnfTM.evalCnfDecidesLang`, over `cnf × assgn`) does not have verbatim:

1. certificates are `List Bool`, not `assgn = List Nat`;
2. `verifier.encodeIn (N, c) = encX N ++ certState c` — the pair layout must
   *split*, with the certificate in the canonical one-register bit layout;
3. `(encX N).length` must be a per-witness **constant** (`xWidth`).

The HANDOFF flagged (2) as the risk, because `EvalCnfCmd.encodeState` is a
12-register literal with **eight trailing scratch `[]`s after** the certificate
register `ASSGN = 3`, so `encodeState (N, a) ≠ encX N ++ certState a` as lists.

**FINDING AD — the trailing scratch registers are invisible, so the layout
factors after all.** The obligation is on the *composite* verifier's `encodeIn`,
and `DecidesLang.precomposeFree` sets that to the `FreePrecomposeData.eIn` we
choose. Choosing

```
satEncX N     = [[], 1^|N|, encodeCnf N]          -- registers 0,1,2; xWidth = 3
satEIn (N, c) = satEncX N ++ certState c          -- the certificate lands on ASSGN
```

makes (2) true *by construction* and (3) true because the list is a literal.
`State.get` reads an unset register as `[]`, so registers `4`–`15` agree with
`encodeState`'s explicit `[]`s automatically: **the entire gap between
`satEIn (N,c)` and `encodeState (N, decodeBits c)` is the single register
`ASSGN`** — raw certificate bits on one side, `encodeAssgn` on the other. There
is no "8 trailing `[]`s" problem and no `xWidth` problem.
`probes/SATSplitProbe.lean` §1 measures this.

Consequently the whole remaining machine obligation is a **one-register
re-encoder**: turn the raw bits at `ASSGN` into `encodeAssgn (decodeBits c)`.

## The certificate semantics

`decodeBits c` is the textbook characteristic vector: variable `i` is true iff
`c[i] = true` (`bitsToAssgn`). It is **total** — every bit string decodes, which
is exactly the "no un-decodable garbage certificate" property
`InNPWitnessLangFreeSplit` was designed around — and it is the shape a machine
wants: one left-to-right pass over the certificate emitting the sentinel-unary
block `[1] ++ 1^i ++ [0]` at each `true`, with the loop's own `forBnd` counter
serving as `1^i`.

## What is left: ONE register equation

A decoder owes three contracts — `CertBridge`, `CertCostBound` and
`Cmd.UsesBelow` — and at the pinned candidate `certDecode` the last two are
already proven (`by decide` through `Cmd.chk`). `CertBridge` in turn splits: the
scratch sits *above* the verifier's frame and the untouched registers are handled
by `Cmd.eval_get_of_not_writes`, so `certBridge_of_decodesAssgn` reduces it to

```lean
∀ N c, State.get (certDecode.eval (satEIn (N, c))) ASSGN = encodeAssgn (decodeBits c)
```

`probes/SATSplitProbe.lean` `#eval`-validates that equation (§2), the end-to-end
decision on satisfying / falsifying / short / over-long / all-garbage
certificates (§3), and the loop invariant a proof would use, at **every** prefix
length (§5). Proving it is ordinary bottom-up loop work with nothing left to
design.
-/

namespace EvalCnfSplit

open Complexity.Lang EvalCnfCmd

/-! ## The certificate semantics (pure) -/

/-- The certificate decode: a bit string is the **characteristic vector** of the
set of variables assigned `true`, so `bitsToAssgn i c` lists the indices `i + j`
at which `c` has a `true`. Total on every bit string — no garbage gap. -/
def bitsToAssgn : Nat → List Bool → assgn
  | _, [] => []
  | i, b :: bs => (if b then [i] else []) ++ bitsToAssgn (i + 1) bs

/-- The certificate decode at offset `0`. -/
def decodeBits (c : List Bool) : assgn := bitsToAssgn 0 c

/-- **The split certificate relation for SAT**: the bit string, read as a
characteristic vector, satisfies the CNF. -/
def satRel (N : cnf) (c : List Bool) : Prop := satisfiesCnf (decodeBits c) N

/-- Membership in the decode, by the position of a `true` cell. -/
theorem mem_bitsToAssgn (c : List Bool) (i v : Nat) :
    v ∈ bitsToAssgn i c ↔ ∃ j, c[j]? = some true ∧ v = i + j := by
  induction c generalizing i with
  | nil =>
      simp only [bitsToAssgn, List.not_mem_nil, false_iff, not_exists]
      intro j
      simp
  | cons b bs ih =>
      show v ∈ (if b then [i] else []) ++ bitsToAssgn (i + 1) bs ↔ _
      rw [List.mem_append, ih (i + 1)]
      constructor
      · rintro (hhd | ⟨j, hj, rfl⟩)
        · have hb : b = true := by
            by_cases h : b
            · exact h
            · simp [h] at hhd
          have hv : v = i := by simp [hb] at hhd; exact hhd
          exact ⟨0, by simp [hb], by omega⟩
        · exact ⟨j + 1, by simpa using hj, by omega⟩
      · rintro ⟨j, hj, rfl⟩
        cases j with
        | zero =>
            have hb : b = true := by simpa using hj
            exact Or.inl (by simp [hb])
        | succ j =>
            refine Or.inr ⟨j, by simpa using hj, by omega⟩

/-! ## `varsOfCnf` bounds — the length of the canonical certificate

A satisfying assignment only has to be spelled out on the variables `N`
mentions, and every such variable is `< encodable.size N`. That makes
`List.range (encodable.size N)` a *uniform* certificate length: no `maxVar`
gadget, and the certificate size bound is linear. -/

/-- An element of an encodable list is smaller than the list. -/
theorem size_add_one_le_of_mem {α : Type} [encodable α] :
    ∀ {x : α} {xs : List α}, x ∈ xs → encodable.size x + 1 ≤ encodable.size xs := by
  intro x xs
  induction xs with
  | nil => intro h; simp at h
  | cons y ys ih =>
      intro hx
      rw [encodable_size_list_cons]
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact Nat.le_add_right _ _
      · exact le_trans (ih hx') (Nat.le_add_left _ _)

/-- Every variable `N` mentions is `< encodable.size N`. -/
theorem varsOfCnf_lt_size {N : cnf} {v : Nat} (hv : v ∈ SAT_inNP.varsOfCnf N) :
    v < encodable.size N := by
  obtain ⟨vc, hvc, hv'⟩ := List.mem_flatten.mp hv
  obtain ⟨C, hCN, hCvc⟩ := List.mem_map.mp hvc
  subst hCvc
  obtain ⟨vl, hvl, hv''⟩ := List.mem_flatten.mp hv'
  obtain ⟨l, hlC, hlvl⟩ := List.mem_map.mp hvl
  subst hlvl
  have hvl2 : v = l.2 := by
    have := List.mem_singleton.mp hv''
    exact this
  have h1 : encodable.size l + 1 ≤ encodable.size C := size_add_one_le_of_mem hlC
  have h2 : encodable.size C + 1 ≤ encodable.size N := size_add_one_le_of_mem hCN
  have h3 : encodable.size l = encodable.size l.1 + l.2 + 1 := rfl
  omega

/-- Two assignments agreeing on every variable `N` mentions satisfy `N`
together. (The `compressAssignment_cnf_equiv` argument, stated generically.) -/
theorem satisfiesCnf_congr_vars {a a' : assgn} (N : cnf)
    (h : ∀ v ∈ SAT_inNP.varsOfCnf N, evalVar a v = evalVar a' v) :
    satisfiesCnf a N ↔ satisfiesCnf a' N := by
  simp only [satisfiesCnf, evalCnf_clause_iff, evalClause_literal_iff]
  apply forall_congr'; intro C; apply imp_congr_right; intro hC
  apply exists_congr; intro l; apply and_congr_right; intro hl
  rcases l with ⟨b, v⟩
  simp only [evalLiteral, h v (SAT_inNP.varsOfCnf_mem N C _ hC hl)]

/-! ## The canonical certificate -/

/-- The canonical certificate of a satisfying assignment: the characteristic
vector of `a` on `[0, encodable.size N)`. -/
def satCert (N : cnf) (a : assgn) : List Bool :=
  (List.range (encodable.size N)).map (fun i => decide (i ∈ a))

theorem satCert_length (N : cnf) (a : assgn) :
    (satCert N a).length = encodable.size N := by
  simp [satCert]

/-- The canonical certificate decodes to `a` restricted to `[0, size N)`. -/
theorem mem_decodeBits_satCert (N : cnf) (a : assgn) (v : Nat) :
    v ∈ decodeBits (satCert N a) ↔ (v < encodable.size N ∧ v ∈ a) := by
  rw [decodeBits, mem_bitsToAssgn]
  constructor
  · rintro ⟨j, hj, rfl⟩
    have hjlt : j < encodable.size N := by
      by_contra hcon
      rw [List.getElem?_eq_none_iff.mpr (by rw [satCert_length]; omega)] at hj
      simp at hj
    rw [satCert, List.getElem?_map, List.getElem?_range hjlt] at hj
    simp only [Option.map_some] at hj
    exact ⟨by omega, by simpa using hj⟩
  · rintro ⟨hlt, hmem⟩
    refine ⟨v, ?_, by omega⟩
    rw [satCert, List.getElem?_map, List.getElem?_range hlt]
    simp [hmem]

/-- **Completeness of the certificate relation**: a satisfiable `N` has a
canonical bit certificate. -/
theorem satRel_satCert {N : cnf} {a : assgn} (ha : satisfiesCnf a N) :
    satRel N (satCert N a) := by
  refine (satisfiesCnf_congr_vars N (fun v hv => ?_)).mp ha
  have hlt : v < encodable.size N := varsOfCnf_lt_size hv
  by_cases hmem : v ∈ a
  · have : v ∈ decodeBits (satCert N a) := (mem_decodeBits_satCert N a v).mpr ⟨hlt, hmem⟩
    simp [evalVar, hmem, this]
  · have : v ∉ decodeBits (satCert N a) := fun hc =>
      hmem ((mem_decodeBits_satCert N a v).mp hc).2
    simp [evalVar, hmem, this]

/-! ## Size accounting -/

/-- A `List Bool` is at least as long as it is big. -/
theorem length_le_size_bool (c : List Bool) : c.length ≤ encodable.size c := by
  induction c with
  | nil => simp [encodable.size]
  | cons b bs ih => rw [encodable_size_list_cons, List.length_cons]; omega

/-- ... and at most twice. -/
theorem size_bool_le_two_length (c : List Bool) :
    encodable.size c ≤ 2 * c.length := by
  induction c with
  | nil => simp [encodable.size]
  | cons b bs ih =>
      have hb : encodable.size b ≤ 1 := by cases b <;> simp [encodable.size]
      rw [encodable_size_list_cons, List.length_cons]
      omega

/-- The certificate size bound of the split relation: linear. -/
theorem size_satCert_le (N : cnf) (a : assgn) :
    encodable.size (satCert N a) ≤ 2 * encodable.size N := by
  have h := size_bool_le_two_length (satCert N a)
  rw [satCert_length] at h
  exact h

/-- The decode's size is at most quadratic — the indices are `< |c|` and each is
listed at most once. -/
theorem size_bitsToAssgn_le (c : List Bool) (i : Nat) :
    encodable.size (bitsToAssgn i c) ≤ c.length * (i + c.length) := by
  induction c generalizing i with
  | nil => simp [bitsToAssgn, encodable.size]
  | cons b bs ih =>
      have ihb := ih (i + 1)
      show encodable.size ((if b then [i] else []) ++ bitsToAssgn (i + 1) bs)
          ≤ (b :: bs).length * (i + (b :: bs).length)
      rw [List.length_cons]
      by_cases hb : b
      · rw [if_pos hb]
        rw [List.singleton_append, encodable_size_list_cons]
        have hi : encodable.size i = i := rfl
        have hexp : (bs.length + 1) * (i + (bs.length + 1))
            = bs.length * (i + 1 + bs.length) + (i + bs.length + 1) := by ring
        omega
      · rw [if_neg hb]
        have hexp : (bs.length + 1) * (i + (bs.length + 1))
            = bs.length * (i + 1 + bs.length) + (i + bs.length + 1) := by ring
        simp only [List.nil_append]
        omega

/-- `size (decodeBits c) ≤ (size c)^2` — the input-size bound the composite's
cost argument needs. -/
theorem size_decodeBits_le (c : List Bool) :
    encodable.size (decodeBits c) ≤ encodable.size c * encodable.size c := by
  have h := size_bitsToAssgn_le c 0
  have hl := length_le_size_bool c
  calc encodable.size (decodeBits c)
      ≤ c.length * (0 + c.length) := h
    _ = c.length * c.length := by ring
    _ ≤ encodable.size c * encodable.size c := Nat.mul_le_mul hl hl

/-! ## The split layout -/

/-- **The input half of the split pair layout** — registers `0`–`2` of the live
verifier's own `encodeState`, and nothing else. Width `3` for every `N`: the
certificate register is the statically-addressable `ASSGN = 3`. -/
def satEncX (N : cnf) : State :=
  [ []                                  -- 0: OUTPUT
  , List.replicate N.length 1           -- 1: CLAUSE_TALLY
  , encodeCnf N ]                       -- 2: CNF_STREAM

/-- **The composite verifier's input encoding.** The split law is definitional. -/
def satEIn (Nc : cnf × List Bool) : State := satEncX Nc.1 ++ certState Nc.2

theorem satEncX_length (N : cnf) : (satEncX N).length = 3 := rfl

theorem satEIn_eq (N : cnf) (c : List Bool) :
    satEIn (N, c) = satEncX N ++ certState c := rfl

/-- `satEIn` is a four-register literal. -/
theorem satEIn_lit (N : cnf) (c : List Bool) :
    satEIn (N, c)
      = [[], List.replicate N.length 1, encodeCnf N,
         c.map (fun b => if b then 1 else 0)] := rfl

theorem satEIn_size (N : cnf) (c : List Bool) :
    State.size (satEIn (N, c)) = N.length + (encodeCnf N).length + c.length := by
  rw [satEIn_lit]
  simp only [State.size, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil,
    List.length_replicate, List.length_nil, List.length_map]
  omega

theorem satEncX_size (N : cnf) :
    State.size (satEncX N) = N.length + (encodeCnf N).length := by
  show State.size [([] : List Nat), List.replicate N.length 1, encodeCnf N] = _
  simp only [State.size, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil,
    List.length_replicate, List.length_nil]
  omega

/-- Both encodings are `BitState`s: unary blocks and `0`/`1` markers only. -/
theorem satEIn_bit (Nc : cnf × List Bool) : Compile.BitState (satEIn Nc) := by
  rcases Nc with ⟨N, c⟩
  rw [satEIn_lit]
  intro reg hreg x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hreg
  rcases hreg with h | h | h | h <;> subst h
  · simp at hx
  · simp only [List.mem_replicate] at hx; omega
  · exact encodeCnf_bit N x hx
  · obtain ⟨b, -, hb⟩ := List.mem_map.mp hx
    rw [← hb]
    cases b <;> simp

/-- The linear size bound on the input half — `6·(size N + 1)`, via the live
verifier's own `encodeState` bound at the empty assignment. -/
theorem satEncX_size_le (N : cnf) :
    State.size (satEncX N) ≤ 6 * (encodable.size N + 1) := by
  have h := encodeState_size_bound (N, ([] : assgn))
  have hs : State.size (encodeState (N, ([] : assgn)))
      = N.length + (encodeCnf N).length + (encodeAssgn ([] : assgn)).length := by
    simp only [encodeState, State.size, List.map_cons, List.map_nil, List.foldr_cons,
      List.foldr_nil, List.length_replicate, List.length_nil]
    omega
  have he : (encodeAssgn ([] : assgn)).length = 0 := by simp [encodeAssgn]
  have hsz : encodable.size ((N, ([] : assgn)) : cnf × assgn) = encodable.size N + 1 := by
    show encodable.size N + encodable.size ([] : assgn) + 1 = _
    simp [encodable.size]
  rw [hs, he, hsz] at h
  rw [satEncX_size]
  omega

theorem satEIn_size_le (N : cnf) (c : List Bool) :
    State.size (satEIn (N, c))
      ≤ 6 * (encodable.size ((N, c) : cnf × List Bool) + 1) := by
  have h1 := satEncX_size_le N
  have h2 := length_le_size_bool c
  have hsz : encodable.size ((N, c) : cnf × List Bool)
      = encodable.size N + encodable.size c + 1 := rfl
  rw [satEIn_size]
  rw [satEncX_size] at h1
  omega

/-! ## `CertDecoder` — the ONE remaining machine obligation

The verifier's register frame is `16` (`EvalCnfTM.evalCnfDecidesLang.regBound`),
and the decoder's scratch may live *above* it: `bridge` only constrains
registers `< 16`, so scratch at `16`, `17`, … needs no scrubbing. That is why
`regBound` is a field rather than a fixed number.

The cost budget is an **existential polynomial** (FINDING Y): a fixed budget
cannot consume a generic cost lemma, whose output is always `∃ K D, K·(M+1)^D`.
State the decoder's cost with `Cmd.CapCost` and close it with `Cmd.chk`
(`by decide`) — `Lang/CostGrow.lean`. -/

/-- **The bridge obligation** — the whole behavioural content of the decoder:
after `dec`, the state agrees with the live verifier's own input layout on the
verifier's whole frame. What a `_run` lemma should actually prove: register
`ASSGN` holds `encodeAssgn (decodeBits c)`, registers `0`–`2` are untouched, and
every other register `< 16` is `[]`. -/
def CertBridge (dec : Cmd) : Prop :=
  ∀ Nc : cnf × List Bool,
    AgreeBelow 16 (dec.eval (satEIn Nc)) (encodeState (Nc.1, decodeBits Nc.2))

/-- **The cost obligation** — an EXISTENTIAL polynomial (FINDING Y): a fixed
budget cannot consume a generic cost lemma, whose output is always
`∃ K D, K·(M+1)^D`. Discharged from a `Cmd.chk` pass by
`certCostBound_of_chk`. -/
def CertCostBound (dec : Cmd) : Prop :=
  ∃ budget : Nat → Nat, inOPoly budget ∧ monotonic budget ∧
    ∀ Nc : cnf × List Bool, dec.cost (satEIn Nc) ≤ budget (encodable.size Nc)

/-! ### The cost obligation is FREE

`Cmd.costLeSize_of_chk` (`Lang/CostGrow.lean`) turns one decidable syntactic
pass into `∃ K D, cost s ≤ K·(size s + 1)^(D+1)`, and `satEIn_size_le` converts
`State.size` into `encodable.size`. So a decoder only ever has to supply the
**bridge**; its cost and frame are `by decide`. (The
`S1Witness.s1CostBound_of_chk` pattern, verbatim.) -/

private theorem inOPoly_pow_succ' (k : Nat) : inOPoly (fun n => (n + 1) ^ k) := by
  refine ⟨k, 2 ^ k, 1, ?_⟩
  intro n hn
  calc (n + 1) ^ k ≤ (2 * n) ^ k := Nat.pow_le_pow_left (by omega) k
    _ = 2 ^ k * n ^ k := by rw [Nat.mul_pow]

theorem certCostBound_of_chk (dec : Cmd) (F : Nat) (h : (dec.chk F).1 = true) :
    CertCostBound dec := by
  obtain ⟨K, D, hb⟩ := Cmd.costLeSize_of_chk dec F h
  refine ⟨fun n => K * 7 ^ (D + 1) * (n + 1) ^ (D + 1),
    inOPoly_mul (inOPoly_const (K * 7 ^ (D + 1))) (inOPoly_pow_succ' (D + 1)),
    fun a b hab => Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _),
    fun Nc => ?_⟩
  rcases Nc with ⟨N, c⟩
  set n := encodable.size ((N, c) : cnf × List Bool) with hn
  have hcost := hb (satEIn (N, c)) (6 * (n + 1)) (satEIn_size_le N c)
  refine le_trans hcost ?_
  have hpow : (6 * (n + 1) + 1) ^ (D + 1) ≤ 7 ^ (D + 1) * (n + 1) ^ (D + 1) := by
    calc (6 * (n + 1) + 1) ^ (D + 1)
        ≤ (7 * (n + 1)) ^ (D + 1) := Nat.pow_le_pow_left (by omega) _
      _ = 7 ^ (D + 1) * (n + 1) ^ (D + 1) := by rw [Nat.mul_pow]
  calc K * (6 * (n + 1) + 1) ^ (D + 1)
      ≤ K * (7 ^ (D + 1) * (n + 1) ^ (D + 1)) := Nat.mul_le_mul_left _ hpow
    _ = K * 7 ^ (D + 1) * (n + 1) ^ (D + 1) := by ring

/-! ## The candidate decoder — PINNED, cost-checked and `#eval`-validated

`certDecode` is a *candidate*: everything downstream is program-generic
(`CertBridge` / `CertCostBound` / `Cmd.UsesBelow` are parameters), so a
bottom-up agent who finds a different program easier to verify may swap it
without touching the assembly. But this one is already known to work:

* `probes/SATSplitProbe.lean` §2/§3 `#eval`-validates its register model
  (`ASSGN = encodeAssgn (decodeBits c)`, cursor drained), the `CertBridge`
  obligation itself, and the end-to-end decision on satisfying / falsifying /
  short / over-long / all-garbage certificates;
* `certDecode_costBound` below is the cost obligation, closed by `by decide`;
* `certDecode_usesBelow` is the frame.

Its scratch (`16`–`18`) sits **above** the verifier's frame `16`, so `CertBridge`
never constrains it and there is nothing to scrub — which is why the decoder
needs no register budget from the verifier at all.

The loop's own `forBnd` counter holds `1^i`, i.e. variable `i` in unary, so no
separate index register is needed. -/

/-- Cursor over the raw certificate bits (destructively consumed). -/
def DCUR : Var := 16
/-- The `forBnd` counter — holds `1^i`, which IS variable `i` in unary. -/
def DIDX : Var := 17
/-- Head-cell / flag scratch. -/
def DHD : Var := 18

/-- One iteration: consume one certificate bit; on `true`, append the
sentinel-unary block `[1] ++ 1^i ++ [0]` for variable `i`. The `nonEmpty` guard
makes the body TOTAL on an exhausted cursor (locked invariant, FINDING T); the
`copy ASSGN ASSGN` else-branch is the layer's no-op (FINDING X — free under
`CapCost`). -/
def decodeBody : Cmd :=
  Cmd.op (.nonEmpty DHD DCUR) ;;
  Cmd.ifBit DHD
    ( Cmd.op (.head DHD DCUR) ;;
      Cmd.op (.tail DCUR DCUR) ;;
      Cmd.ifBit DHD
        ( Cmd.op (.appendOne ASSGN) ;;
          Cmd.op (.concat ASSGN ASSGN DIDX) ;;
          Cmd.op (.appendZero ASSGN) )
        (Cmd.op (.copy ASSGN ASSGN)) )
    (Cmd.op (.copy DCUR DCUR))

/-- The candidate re-encoder: move the raw bits out to the cursor, empty
`ASSGN`, then emit one block per `true` bit. The loop's bound register is the
cursor itself, and `forBnd` samples it ONCE at entry, so the trip count is
exactly `|c|`. -/
def certDecode : Cmd :=
  Cmd.op (.copy DCUR ASSGN) ;;
  Cmd.op (.clear ASSGN) ;;
  Cmd.forBnd DIDX DCUR decodeBody

/-- The `Cmd.chk` seed mask: at entry every register `< 19` is bounded by the
input size. -/
def decRegs : Nat := 2 ^ 19 - 1

/-- **The candidate's cost obligation — one decidable syntactic pass.** -/
theorem certDecode_chk : (certDecode.chk decRegs).1 = true := by decide

theorem certDecode_costBound : CertCostBound certDecode :=
  certCostBound_of_chk certDecode decRegs certDecode_chk

theorem certDecode_usesBelow : Cmd.UsesBelow certDecode 19 := by
  simp [certDecode, decodeBody, Cmd.UsesBelow, Op.UsesBelow, DCUR, DIDX, DHD,
    ASSGN]

/-! ### The bridge reduces to ONE register equation

`certDecode.writes = {ASSGN, DCUR, DIDX, DHD}`, so registers `0`–`2` and
`4`–`15` are untouched by construction (`Cmd.eval_get_of_not_writes`) and already
agree with `encodeState`. The *entire* behavioural obligation is therefore the
single equation on register `ASSGN`. -/

/-- **The whole remaining membership obligation.** Note it mentions no other
register and no `AgreeBelow`: the frame half is discharged below. -/
def DecodesAssgn (dec : Cmd) : Prop :=
  ∀ (N : cnf) (c : List Bool),
    State.get (dec.eval (satEIn (N, c))) ASSGN = encodeAssgn (decodeBits c)

/-- **The frame half of the bridge, for free.** `certDecode` writes only
`ASSGN`, `DCUR`, `DIDX`, `DHD`; the latter three are `≥ 16`, so every register
the verifier reads except `ASSGN` still holds exactly what `satEIn` put there —
which is what `encodeState` has. -/
theorem certBridge_of_decodesAssgn (h : DecodesAssgn certDecode) :
    CertBridge certDecode := by
  rintro ⟨N, c⟩ r hr
  have hframe : ∀ q : Var, q ∉ certDecode.writes →
      State.get (certDecode.eval (satEIn (N, c))) q = State.get (satEIn (N, c)) q :=
    fun q hq => Cmd.eval_get_of_not_writes certDecode _ q hq
  interval_cases r
  · rw [hframe 0 (by decide)]; rfl
  · rw [hframe 1 (by decide)]; rfl
  · rw [hframe 2 (by decide)]; rfl
  · exact h N c
  · rw [hframe 4 (by decide)]; rfl
  · rw [hframe 5 (by decide)]; rfl
  · rw [hframe 6 (by decide)]; rfl
  · rw [hframe 7 (by decide)]; rfl
  · rw [hframe 8 (by decide)]; rfl
  · rw [hframe 9 (by decide)]; rfl
  · rw [hframe 10 (by decide)]; rfl
  · rw [hframe 11 (by decide)]; rfl
  · rw [hframe 12 (by decide)]; rfl
  · rw [hframe 13 (by decide)]; rfl
  · rw [hframe 14 (by decide)]; rfl
  · rw [hframe 15 (by decide)]; rfl

/-! ### Atoms for the bridge proof

The `_run` lemma the bridge needs is an `S1Step.emitFold_run`-style invariant:
after `i` iterations `DCUR` holds the mapped `c.drop i` and `ASSGN` holds
`encodeAssgn (decodeBits (c.take i))`. These three equations are its step. -/

/-- `bitsToAssgn` splits over `++`, with the offset shifted by the prefix. -/
theorem bitsToAssgn_append (c d : List Bool) (i : Nat) :
    bitsToAssgn i (c ++ d) = bitsToAssgn i c ++ bitsToAssgn (i + c.length) d := by
  induction c generalizing i with
  | nil => simp [bitsToAssgn]
  | cons b bs ih =>
      show (if b then [i] else []) ++ bitsToAssgn (i + 1) (bs ++ d)
          = ((if b then [i] else []) ++ bitsToAssgn (i + 1) bs)
            ++ bitsToAssgn (i + (bs.length + 1)) d
      have hi : i + 1 + bs.length = i + (bs.length + 1) := by omega
      rw [ih (i + 1), List.append_assoc, hi]

/-- **The loop's step on the model side**: one more certificate cell adds one
variable, or nothing. -/
theorem decodeBits_take_succ (c : List Bool) (i : Nat) (h : i < c.length) :
    decodeBits (c.take (i + 1))
      = decodeBits (c.take i) ++ (if c[i] then [i] else []) := by
  have htake : c.take (i + 1) = c.take i ++ [c[i]] := by
    rw [List.take_add_one, List.getElem?_eq_getElem h]
    rfl
  have hlen : (c.take i).length = i := by
    rw [List.length_take]; omega
  rw [decodeBits, htake, bitsToAssgn_append, hlen]
  show decodeBits (c.take i) ++ bitsToAssgn (0 + i) [c[i]] = _
  congr 1
  show (if c[i] then [0 + i] else []) ++ bitsToAssgn (0 + i + 1) [] = _
  simp [bitsToAssgn]

/-- `encodeAssgn` splits over `++` — the machine appends one block per `true`. -/
theorem encodeAssgn_append (a b : assgn) :
    encodeAssgn (a ++ b) = encodeAssgn a ++ encodeAssgn b := by
  induction a with
  | nil => simp [encodeAssgn]
  | cons u a ih =>
      show (1 :: (List.replicate u 1 ++ [0])) ++ encodeAssgn (a ++ b)
          = ((1 :: (List.replicate u 1 ++ [0])) ++ encodeAssgn a) ++ encodeAssgn b
      rw [ih, List.append_assoc]

/-- The block the machine appends for variable `v` — `appendOne`, `concat` with
the loop counter `1^v`, `appendZero`. -/
theorem encodeAssgn_singleton (v : Nat) :
    encodeAssgn [v] = (1 :: List.replicate v 1) ++ [0] := by
  show (1 :: (List.replicate v 1 ++ [0])) ++ encodeAssgn ([] : assgn) = _
  simp [encodeAssgn]

/-! ## The composite's polynomial -/

/-- The verifier's input size after decoding, as a function of the pair size:
`size (N, decodeBits c) ≤ n^2 + 1` where `n = size (N, c)`. -/
theorem size_decoded_le (N : cnf) (c : List Bool) :
    encodable.size ((N, decodeBits c) : cnf × assgn)
      ≤ encodable.size ((N, c) : cnf × List Bool)
        * encodable.size ((N, c) : cnf × List Bool) := by
  have h := size_decodeBits_le c
  have hd : encodable.size ((N, decodeBits c) : cnf × assgn)
      = encodable.size N + encodable.size (decodeBits c) + 1 := rfl
  have hn : encodable.size ((N, c) : cnf × List Bool)
      = encodable.size N + encodable.size c + 1 := rfl
  rw [hd, hn]
  nlinarith [Nat.zero_le (encodable.size N), Nat.zero_le (encodable.size c)]

/-- The composite decider's cost/size bound: the decoder's budget plus the
verifier's quartic at the squared argument. -/
def satNewBound (budget : Nat → Nat) (n : Nat) : Nat :=
  budget n + EvalCnfTM.timeBound (n * n) + 1

theorem satNewBound_poly {budget : Nat → Nat} (h : inOPoly budget) :
    inOPoly (satNewBound budget) := by
  have hsq : inOPoly (fun n => n * n) := inOPoly_mul inOPoly_id inOPoly_id
  have hcomp : inOPoly (fun n => EvalCnfTM.timeBound (n * n)) :=
    inOPoly_comp (f := fun n => n * n) (g := EvalCnfTM.timeBound) hsq
      EvalCnfTM.timeBound_inOPoly
  exact inOPoly_add (inOPoly_add h hcomp) (inOPoly_const 1)

theorem satNewBound_mono {budget : Nat → Nat} (h : monotonic budget) :
    monotonic (satNewBound budget) := by
  intro a b hab
  have h1 : budget a ≤ budget b := h a b hab
  have h2 : EvalCnfTM.timeBound (a * a) ≤ EvalCnfTM.timeBound (b * b) :=
    EvalCnfTM.timeBound_monotonic _ _ (Nat.mul_le_mul hab hab)
  show budget a + _ + 1 ≤ budget b + _ + 1
  omega

/-- `6·(n+1) ≤ timeBound (n·n)` — the slack that lets the composite's bound
absorb both `encodeIn_size` obligations. -/
theorem six_le_timeBound (n : Nat) : 6 * (n + 1) ≤ EvalCnfTM.timeBound (n * n) := by
  show 6 * (n + 1) ≤ 200000 * (n * n + 1) ^ 4
  have h1 : n * n + 1 ≤ (n * n + 1) ^ 4 := Nat.le_self_pow (by norm_num) _
  have h2 : n + 1 ≤ n * n + 1 := by nlinarith
  calc 6 * (n + 1) ≤ 200000 * (n + 1) := by omega
    _ ≤ 200000 * (n * n + 1) := Nat.mul_le_mul_left _ h2
    _ ≤ 200000 * (n * n + 1) ^ 4 := Nat.mul_le_mul_left _ h1

/-! ## The composite verifier -/

/-- The pair map the re-encoder implements: keep the CNF, decode the bits. -/
def gDecode (Nc : cnf × List Bool) : cnf × assgn := (Nc.1, decodeBits Nc.2)

/-- **The `FreePrecomposeData` for the SAT membership re-encoding.** `eIn` is the
SPLIT layout (`satEIn`), not `encodeState ∘ gDecode`: all the decode work is in
`dec`, and the certificate register is the canonical `certState` — the honesty
discipline of standing risk #1. -/
noncomputable def satPrecomposeData (dec : Cmd) (rb : Nat) (hrb : 16 ≤ rb)
    (hbridge : CertBridge dec) (hcost : CertCostBound dec)
    (huses : Cmd.UsesBelow dec rb) :
    EvalCnfTM.evalCnfDecidesLang.FreePrecomposeData gDecode where
  mfc := dec
  eIn := satEIn
  newBound := satNewBound hcost.choose
  newBound_poly := satNewBound_poly hcost.choose_spec.1
  newBound_mono := satNewBound_mono hcost.choose_spec.2.1
  bridge := hbridge
  encodeIn_size := fun v => by
    rcases v with ⟨N, c⟩
    have h1 := satEIn_size_le N c
    have h2 := six_le_timeBound (encodable.size ((N, c) : cnf × List Bool))
    show _ ≤ hcost.choose _ + EvalCnfTM.timeBound (_ * _) + 1
    omega
  cost_bound := fun v => by
    rcases v with ⟨N, c⟩
    set n := encodable.size ((N, c) : cnf × List Bool) with hn
    have hcost1 : dec.cost (satEIn (N, c)) ≤ hcost.choose n :=
      hcost.choose_spec.2.2 (N, c)
    have hcost2 : evalCnfCmd.cost (dec.eval (satEIn (N, c)))
        = evalCnfCmd.cost (encodeState (N, decodeBits c)) :=
      Cmd.cost_agree _ 16 evalCnfCmd_usesBelow (hbridge (N, c))
    have hcost3 : evalCnfCmd.cost (encodeState (N, decodeBits c))
        ≤ EvalCnfTM.timeBound (n * n) :=
      le_trans (evalCnfCmd_cost_bound _)
        (EvalCnfTM.timeBound_monotonic _ _ (by rw [hn]; exact size_decoded_le N c))
    show (dec ;; evalCnfCmd).cost (satEIn (N, c)) ≤ satNewBound hcost.choose n
    rw [Cmd.cost_seq, hcost2]
    show 1 + dec.cost (satEIn (N, c)) + _
        ≤ hcost.choose n + EvalCnfTM.timeBound (n * n) + 1
    omega
  enc_bit := satEIn_bit
  regBound := rb
  usesBelow := ⟨huses, Cmd.UsesBelow_mono hrb evalCnfCmd_usesBelow⟩
  width_le := fun v => by
    rcases v with ⟨N, c⟩
    show (satEIn (N, c)).length ≤ rb
    rw [satEIn_lit]
    simp only [List.length_cons, List.length_nil]
    omega

/-- **The split verifier for SAT.** `encodeIn` is `satEIn`, so
`encodeIn (N, c) = satEncX N ++ certState c` holds by `rfl`. -/
noncomputable def satSplitVerifier (dec : Cmd) (rb : Nat) (hrb : 16 ≤ rb)
    (hbridge : CertBridge dec) (hcost : CertCostBound dec)
    (huses : Cmd.UsesBelow dec rb) :
    DecidesLang (fun Nc : cnf × List Bool => satRel Nc.1 Nc.2)
      (satNewBound hcost.choose) :=
  EvalCnfTM.evalCnfDecidesLang.precomposeFree gDecode
    (satPrecomposeData dec rb hrb hbridge hcost huses)

/-! ## The witness -/

/-- **`polyCertRel SAT satRel`** — the pure NP content of the membership half:
the bit-string certificate relation is sound, complete and linearly bounded.
No machine, no `sorry`. -/
theorem satRel_correct : polyCertRel SAT satRel :=
  ⟨⟨fun n => 2 * n,
    fun {N} {c} h => ⟨decodeBits c, h⟩,
    fun {N} hN => by
      obtain ⟨a, ha⟩ := hN
      exact ⟨satCert N a, satRel_satCert ha, size_satCert_le N a⟩,
    inOPoly_mul (inOPoly_const 2) inOPoly_id,
    fun _ _ hab => Nat.mul_le_mul_left 2 hab⟩⟩

/-- **`InNPWitnessLangFreeSplit SAT` from the decoder contracts alone.**
Everything else is discharged; the statement is axiom-clean, so it is a
machine-checked statement of exactly what the membership half still needs:
*one* `Cmd` re-encoding *one* register. -/
noncomputable def satSplitWitnessOf (dec : Cmd) (rb : Nat) (hrb : 16 ≤ rb)
    (hbridge : CertBridge dec) (hcost : CertCostBound dec)
    (huses : Cmd.UsesBelow dec rb) :
    InNPWitnessLangFreeSplit SAT where
  rel := satRel
  dBound := satNewBound hcost.choose
  dBound_poly := satNewBound_poly hcost.choose_spec.1
  dBound_mono := satNewBound_mono hcost.choose_spec.2.1
  verifier := satSplitVerifier dec rb hrb hbridge hcost huses
  rel_correct := satRel_correct
  encX := satEncX
  encodeIn_eq := fun _ _ => rfl
  xWidth := 3
  encX_width := satEncX_length
  encX_size := fun N => by
    have h1 := satEncX_size_le N
    have h2 := six_le_timeBound (encodable.size N)
    show _ ≤ hcost.choose _ + EvalCnfTM.timeBound (_ * _) + 1
    omega

/-- **`inNPLangFreeSplit SAT` from the decoder contracts alone** — the membership
half of `NPcomplete'' SAT`. -/
theorem SAT_inNPLangFreeSplit_of (dec : Cmd) (rb : Nat) (hrb : 16 ≤ rb)
    (hbridge : CertBridge dec) (hcost : CertCostBound dec)
    (huses : Cmd.UsesBelow dec rb) : inNPLangFreeSplit SAT :=
  ⟨satSplitWitnessOf dec rb hrb hbridge hcost huses⟩

/-- **... at the pinned candidate decoder**: the bridge is the ONLY input. -/
theorem SAT_inNPLangFreeSplit_of_bridge (hbridge : CertBridge certDecode) :
    inNPLangFreeSplit SAT :=
  SAT_inNPLangFreeSplit_of certDecode 19 (by omega) hbridge certDecode_costBound
    certDecode_usesBelow

/-- **`inNPLangFreeSplit SAT` from ONE register equation.** This is the whole
remaining membership half of Cook–Levin. -/
theorem SAT_inNPLangFreeSplit_of_decodesAssgn (h : DecodesAssgn certDecode) :
    inNPLangFreeSplit SAT :=
  SAT_inNPLangFreeSplit_of_bridge (certBridge_of_decodesAssgn h)

end EvalCnfSplit
