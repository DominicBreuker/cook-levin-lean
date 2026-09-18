import CookLevin.SAT.EvalCnfTM
import CookLevin.SAT.CnfSerialize
import CookLevin.Lang.CostGrow

/-!
# SAT as a verifier problem

The certificate relation `satRel N c` (the bit string `c` encodes an assignment satisfying
`N`), its polynomial certificate bound `satCert`, the decoder program `certDecode` that
turns the certificate bits into the assignment layout of `evalCnfCmd`, and
`satRel_correct : SAT N ↔ ∃ c, satRel N c`.
-/

set_option autoImplicit false

namespace EvalCnfSplit

open CookLevin.Lang EvalCnfCmd

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

/-! ## `CertDecoder` — the ONE remaining machine obligation

The verifier's register frame is `16` (`EvalCnfTM.evalCnfDecidesLang.regBound`),
and the decoder's scratch may live *above* it: `bridge` only constrains
registers `< 16`, so scratch at `16`, `17`, … needs no scrubbing. That is why
`regBound` is a field rather than a fixed number.

The cost budget is an **existential polynomial**: a fixed budget
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

/-! ### The cost obligation is FREE

`Cmd.costLeSize_of_chk` (`Lang/CostGrow.lean`) turns one decidable syntactic
pass into `∃ K D, cost s ≤ K·(size s + 1)^(D+1)`, and `satEIn_size_le` converts
`State.size` into `encodable.size`. So a decoder only ever has to supply the
**bridge**; its cost and frame are `by decide`. (The
`S1Witness.s1CostBound_of_chk` pattern, verbatim.) -/

/-! ## The decoder

`certDecode` turns the certificate bits into the assignment layout `encodeAssgn` of the
verifier. Everything downstream is stated over the three contracts `CertBridge`,
`CertCostBound` and `Cmd.UsesBelow`; `certDecode_bridge`, `certDecode_costBound` and
`certDecode_usesBelow` discharge them.

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
makes the body TOTAL on an exhausted cursor; the
`copy ASSGN ASSGN` else-branch is the layer's no-op. -/
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

/-! ### The decoder's `_run` lemma

Three steps, in the `S1Step.emitFold_run` shape:

* `decodeBody_run` — one iteration, at `i < |c|`, moves the invariant from `i` to
  `i + 1`. Both arms of the inner `ifBit` are needed: a `true` bit appends
  `encodeAssgn [i]` (the machine's `appendOne` / `concat … DIDX` / `appendZero`
  is *exactly* `encodeAssgn_singleton`, with the loop counter supplying `1^i`),
  a `false` bit runs the `copy ASSGN ASSGN` no-op and the model's
  `decodeBits_take_succ` contributes `[]`. The outer `nonEmpty DHD DCUR` guard
  is *discharged*, never taken: at
  `i < |c|` the cursor is a cons.
* `certDecode_eval_eq` — the two prologue ops and `Cmd.eval_forBnd`, with the
  trip count pinned at `|c|` (`forBnd` samples `DCUR` once, at entry).
* `certDecode_decodesAssgn` — `Cmd.foldlState_range_induct` at the invariant,
  read off at `i = |c|` via `List.take_length`. -/

/-- The machine's view of a certificate: one `0`/`1` cell per bit. This is the
content of `certState c`'s only register, and what `DCUR` carries. -/
def cbits (c : List Bool) : List Nat := c.map (fun b => if b then 1 else 0)

/-- The cursor, one iteration in: the cell the body pops, then the rest. -/
theorem cbits_drop_succ (c : List Bool) (i : Nat) (h : i < c.length) :
    cbits (c.drop i) = (if c[i] then 1 else 0) :: cbits (c.drop (i + 1)) := by
  rw [cbits, cbits, List.drop_eq_getElem_cons h, List.map_cons]

/-- **One iteration of the decode loop.** Given the invariant at `i` (and the
loop counter at `1^i`, which `forBnd` supplies), `decodeBody` establishes it at
`i + 1`. Only `ASSGN` and `DCUR` are constrained: the frame is
`Cmd.eval_get_of_not_writes`'s job, not the loop's. -/
theorem decodeBody_run (c : List Bool) (i : Nat) (hi : i < c.length) (s : State)
    (hA : State.get s ASSGN = encodeAssgn (decodeBits (c.take i)))
    (hC : State.get s DCUR = cbits (c.drop i))
    (hI : State.get s DIDX = List.replicate i 1) :
    State.get (decodeBody.eval s) ASSGN = encodeAssgn (decodeBits (c.take (i + 1)))
      ∧ State.get (decodeBody.eval s) DCUR = cbits (c.drop (i + 1)) := by
  have hne : State.get s DCUR = (if c[i] then 1 else 0) :: cbits (c.drop (i + 1)) := by
    rw [hC, cbits_drop_succ c i hi]
  -- the totality guard: the cursor is non-empty, so the body takes its true arm
  have e1 : (Cmd.op (Op.nonEmpty DHD DCUR)).eval s = s.set DHD [1] := by
    show s.set DHD (if (State.get s DCUR).isEmpty then [0] else [1]) = _
    rw [hne]; rfl
  rw [decodeBody, Cmd.eval_seq, e1,
    Cmd.eval_ifBit_true _ _ _ _ (State.get_set_eq s DHD [1])]
  -- pop the leading cell into `DHD`, advance the cursor
  have hDCUR1 : State.get (s.set DHD [1]) DCUR
      = (if c[i] then 1 else 0) :: cbits (c.drop (i + 1)) := by
    rw [State.get_set_ne s DHD [1] DCUR (by decide)]; exact hne
  have e2 : (Cmd.op (Op.head DHD DCUR)).eval (s.set DHD [1])
      = s.set DHD [if c[i] then 1 else 0] := by
    simp only [Cmd.eval_op, Op.eval, hDCUR1, State.set_set]
  have hDCUR2 : State.get (s.set DHD [if c[i] then 1 else 0]) DCUR
      = (if c[i] then 1 else 0) :: cbits (c.drop (i + 1)) := by
    rw [State.get_set_ne s DHD _ DCUR (by decide)]; exact hne
  have e3 : (Cmd.op (Op.tail DCUR DCUR)).eval (s.set DHD [if c[i] then 1 else 0])
      = (s.set DHD [if c[i] then 1 else 0]).set DCUR (cbits (c.drop (i + 1))) := by
    simp only [Cmd.eval_op, Op.eval, hDCUR2, List.tail_cons]
  rw [Cmd.eval_seq, e2, Cmd.eval_seq, e3]
  -- `t`: the state the inner `ifBit` branches on
  set t : State :=
    (s.set DHD [if c[i] then 1 else 0]).set DCUR (cbits (c.drop (i + 1))) with ht
  have hT_DCUR : State.get t DCUR = cbits (c.drop (i + 1)) := State.get_set_eq _ _ _
  have hT_ASSGN : State.get t ASSGN = encodeAssgn (decodeBits (c.take i)) := by
    rw [ht, State.get_set_ne _ DCUR _ ASSGN (by decide),
      State.get_set_ne _ DHD _ ASSGN (by decide)]
    exact hA
  have hT_DIDX : State.get t DIDX = List.replicate i 1 := by
    rw [ht, State.get_set_ne _ DCUR _ DIDX (by decide),
      State.get_set_ne _ DHD _ DIDX (by decide)]
    exact hI
  have hT_DHD : State.get t DHD = [if c[i] then 1 else 0] := by
    rw [ht, State.get_set_ne _ DCUR _ DHD (by decide)]
    exact State.get_set_eq _ _ _
  by_cases hbi : c[i] = true
  · -- a `true` bit: append the block `[1] ++ 1^i ++ [0]`, i.e. `encodeAssgn [i]`
    rw [Cmd.eval_ifBit_true _ _ _ _ (by rw [hT_DHD, if_pos hbi])]
    have a1 : (Cmd.op (Op.appendOne ASSGN)).eval t
        = t.set ASSGN (encodeAssgn (decodeBits (c.take i)) ++ [1]) := by
      simp only [Cmd.eval_op, Op.eval, hT_ASSGN]
    have hI2 : State.get (t.set ASSGN (encodeAssgn (decodeBits (c.take i)) ++ [1])) DIDX
        = List.replicate i 1 := by
      rw [State.get_set_ne _ ASSGN _ DIDX (by decide)]; exact hT_DIDX
    have a2 : (Cmd.op (Op.concat ASSGN ASSGN DIDX)).eval
          (t.set ASSGN (encodeAssgn (decodeBits (c.take i)) ++ [1]))
        = t.set ASSGN ((encodeAssgn (decodeBits (c.take i)) ++ [1]) ++ List.replicate i 1) := by
      simp only [Cmd.eval_op, Op.eval, hI2, State.get_set_eq, State.set_set]
    have a3 : (Cmd.op (Op.appendZero ASSGN)).eval
          (t.set ASSGN ((encodeAssgn (decodeBits (c.take i)) ++ [1]) ++ List.replicate i 1))
        = t.set ASSGN
            (((encodeAssgn (decodeBits (c.take i)) ++ [1]) ++ List.replicate i 1) ++ [0]) := by
      simp only [Cmd.eval_op, Op.eval, State.get_set_eq, State.set_set]
    rw [Cmd.eval_seq, a1, Cmd.eval_seq, a2, a3]
    refine ⟨?_, ?_⟩
    · rw [State.get_set_eq, decodeBits_take_succ c i hi, if_pos hbi,
        encodeAssgn_append, encodeAssgn_singleton]
      simp
    · rw [State.get_set_ne _ ASSGN _ DCUR (by decide)]; exact hT_DCUR
  · -- a `false` bit: the `copy ASSGN ASSGN` no-op
    rw [Cmd.eval_ifBit_false _ _ _ _ (by rw [hT_DHD, if_neg hbi]; simp)]
    have a1 : (Cmd.op (Op.copy ASSGN ASSGN)).eval t
        = t.set ASSGN (encodeAssgn (decodeBits (c.take i))) := by
      simp only [Cmd.eval_op, Op.eval, hT_ASSGN]
    rw [a1]
    refine ⟨?_, ?_⟩
    · rw [State.get_set_eq, decodeBits_take_succ c i hi, if_neg hbi]
      simp
    · rw [State.get_set_ne _ ASSGN _ DCUR (by decide)]; exact hT_DCUR

/-- The state `certDecode`'s loop starts from: the bits moved out to the cursor,
`ASSGN` emptied. -/
def loopStart (N : cnf) (c : List Bool) : State :=
  ((satEIn (N, c)).set DCUR (cbits c)).set ASSGN []

/-- **The prologue and the trip count.** `forBnd` samples `DCUR` once at entry,
and at entry `DCUR` holds the whole certificate — so the loop runs exactly `|c|`
times. -/
theorem certDecode_eval_eq (N : cnf) (c : List Bool) :
    certDecode.eval (satEIn (N, c))
      = Cmd.foldlState decodeBody DIDX (List.range c.length) (loopStart N c) := by
  have h0 : State.get (satEIn (N, c)) ASSGN = cbits c := rfl
  have e1 : (Cmd.op (Op.copy DCUR ASSGN)).eval (satEIn (N, c))
      = (satEIn (N, c)).set DCUR (cbits c) := by
    simp only [Cmd.eval_op, Op.eval, h0]
  have hd : State.get (loopStart N c) DCUR = cbits c := by
    rw [loopStart, State.get_set_ne _ ASSGN _ DCUR (by decide), State.get_set_eq]
  rw [certDecode, Cmd.eval_seq, e1, Cmd.eval_seq]
  show (Cmd.forBnd DIDX DCUR decodeBody).eval (loopStart N c) = _
  rw [Cmd.eval_forBnd, hd]
  simp [cbits]

/-- **THE remaining Cook–Levin obligation, discharged.** `certDecode` re-encodes
the raw certificate bits at `ASSGN` into the live verifier's `encodeAssgn`
layout. With `certBridge_of_decodesAssgn` this closes `CertBridge certDecode`,
hence `inNPLangFreeSplit SAT`, hence `NPcomplete'' SAT`. -/
theorem certDecode_decodesAssgn : DecodesAssgn certDecode := by
  intro N c
  have hA0 : State.get (loopStart N c) ASSGN = encodeAssgn (decodeBits (c.take 0)) := by
    rw [loopStart, State.get_set_eq]; rfl
  have hC0 : State.get (loopStart N c) DCUR = cbits (c.drop 0) := by
    rw [loopStart, State.get_set_ne _ ASSGN _ DCUR (by decide), State.get_set_eq]
    simp
  have key := Cmd.foldlState_range_induct decodeBody DIDX c.length (loopStart N c)
    (fun i st => State.get st ASSGN = encodeAssgn (decodeBits (c.take i))
      ∧ State.get st DCUR = cbits (c.drop i))
    ⟨hA0, hC0⟩
    (by
      rintro i st hi ⟨hA, hC⟩
      refine decodeBody_run c i hi _ ?_ ?_ (State.get_set_eq _ _ _)
      · rw [State.get_set_ne _ DIDX _ ASSGN (by decide)]; exact hA
      · rw [State.get_set_ne _ DIDX _ DCUR (by decide)]; exact hC)
  rw [certDecode_eval_eq]
  have hfin := key.1
  rwa [List.take_length] at hfin

/-- The bridge at the pinned candidate — unconditional. -/
theorem certDecode_bridge : CertBridge certDecode :=
  certBridge_of_decodesAssgn certDecode_decodesAssgn

/-! ## The composite's polynomial -/

/-! ## The composite verifier -/

/-! ## The witness -/

/-- **`polyCertRel SAT satRel`** — the pure NP content of the membership half:
the bit-string certificate relation is sound, complete and linearly bounded.
No machine is involved. -/
theorem satRel_correct : polyCertRel SAT satRel :=
  ⟨⟨fun n => 2 * n,
    fun {N} {c} h => ⟨decodeBits c, h⟩,
    fun {N} hN => by
      obtain ⟨a, ha⟩ := hN
      exact ⟨satCert N a, satRel_satCert ha, size_satCert_le N a⟩,
    inOPoly_mul (inOPoly_const 2) inOPoly_id,
    fun _ _ hab => Nat.mul_le_mul_left 2 hab⟩⟩

end EvalCnfSplit
