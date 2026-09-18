import CookLevin.Reductions.S1Program
import CookLevin.Lang.CostGrow
import CookLevin.Lang.CostGrowHole

/-!
# FlatSingleTMGenNP ⪯p FlatTCC: the witness

The program witness `s1_reductionLang` for `S1Map.s1Map`, computed by
`S1Program.s1Program`. The size bounds are proved directly. The cost bound is obtained
from the decidable certificate `Cmd.chk` (`Lang/CostGrow.lean`): the program is far too
large for one kernel evaluation, so it is split along the hole decomposition of
`Lang/CostGrowHole.lean` into the innermost prelude loops (`K3`, `K2`, `kindNest`) and the
remaining shape `progH`, each checked by `decide`, and `s1Program_chk` assembles the
pieces.
-/

set_option autoImplicit false
set_option maxRecDepth 4000000
set_option maxHeartbeats 4000000

namespace S1Witness

open CookLevin.Lang

/-! ## The output key (= `FlatTCCFree.encodeIn` registers 1–5)

`s1Key` / `s1Extract` / `SIGMA`…`STEPS` / `s1RegBound` are defined in
`Reductions/S1Program.lean`; their injectivity is proved here. -/

open S1Program (s1Key s1Extract SIGMA INIT CARDS FINAL STEPS s1RegBound)

/-! ### Injectivity of the output key

`decodeOut = Function.invFun s1Key` inverts the key only if `s1Key` determines the
`FlatTCC`. `encNats`/`encFinal`
injectivity are proven in `FlatTCC_to_FlatCC_free.lean`; the card stream
(`encCardsIn`, 6 bare blocks per card, no sentinels) needs its own argument —
fixed arity is what makes it decodable. -/

theorem encNats_append (xs ys : List Nat) :
    FlatTCCFree.encNats (xs ++ ys)
      = FlatTCCFree.encNats xs ++ FlatTCCFree.encNats ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      show FlatTCCFree.encNat x ++ FlatTCCFree.encNats (xs ++ ys)
        = (FlatTCCFree.encNat x ++ FlatTCCFree.encNats xs) ++ _
      rw [ih, List.append_assoc]

/-- The card stream is `encNats` of the flattened 6-nat blocks. -/
theorem encCardsIn_eq (cs : List (TCCCard Nat)) :
    FlatTCCFree.encCardsIn cs
      = FlatTCCFree.encNats (cs.flatMap FlatTCCFree.cardNats) := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
      show FlatTCCFree.encCardIn c ++ FlatTCCFree.encCardsIn cs = _
      rw [ih, List.flatMap_cons, encNats_append]
      rfl

/-- A card is determined by its six nats. -/
theorem cardNats_injective : Function.Injective FlatTCCFree.cardNats := by
  intro a b h
  simp only [FlatTCCFree.cardNats, List.cons.injEq, and_true] at h
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  cases a with
  | mk ap ac =>
    cases b with
    | mk bp bc =>
      cases ap; cases ac; cases bp; cases bc
      simp_all

/-- `flatMap` of a constant-length-6 function is injective. -/
theorem flatMap_cardNats_injective :
    Function.Injective (fun cs : List (TCCCard Nat) => cs.flatMap FlatTCCFree.cardNats) := by
  intro cs
  induction cs with
  | nil =>
      intro ds h
      cases ds with
      | nil => rfl
      | cons d ds =>
          exfalso
          have hlen := congrArg List.length h
          simp only [List.flatMap_nil, List.flatMap_cons, List.length_nil,
            List.length_append] at hlen
          have : (FlatTCCFree.cardNats d).length = 6 := rfl
          omega
  | cons c cs ih =>
      intro ds h
      cases ds with
      | nil =>
          exfalso
          have hlen := congrArg List.length h
          simp only [List.flatMap_nil, List.flatMap_cons, List.length_nil,
            List.length_append] at hlen
          have : (FlatTCCFree.cardNats c).length = 6 := rfl
          omega
      | cons d ds =>
          simp only [List.flatMap_cons] at h
          have hc : (FlatTCCFree.cardNats c).length = (FlatTCCFree.cardNats d).length := rfl
          obtain ⟨h1, h2⟩ := (List.append_inj h hc)
          rw [cardNats_injective h1, ih h2]

theorem encCardsIn_injective : Function.Injective FlatTCCFree.encCardsIn := by
  intro cs ds h
  rw [encCardsIn_eq, encCardsIn_eq] at h
  exact flatMap_cardNats_injective (FlatTCCFree.encNats_injective h)

/-- **The output layout is decodable.** -/
theorem s1Key_injective : Function.Injective s1Key := by
  intro a b h
  simp only [S1Program.s1Key, List.cons.injEq, and_true] at h
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  cases a with
  | mk aS ai ac af ast =>
    cases b with
    | mk bS bi bc bf bst =>
      simp only at h1 h2 h3 h4 h5
      have e1 : aS = bS := NumGadgets.replicate_one_eq_iff.mp h1
      have e5 : ast = bst := NumGadgets.replicate_one_eq_iff.mp h5
      rw [e1, e5, FlatTCCFree.encNats_injective h2, encCardsIn_injective h3,
        FlatTCCFree.encFinal_injective h4]

/-! ## The input-encoding size bound

`PolyTimeComputableLang.encodeIn_size` wants
`State.size (headEncodeIn x) ≤ encBound (encodable.size x)` with `encBound`
polynomial. -/

/-- The sentinel item stream's length: one `1`, `v` ones, one `0` per value. -/
theorem encSyms_length (l : List Nat) :
    (HeadLayout.encSyms l).length = l.sum + 2 * l.length := by
  induction l using List.reverseRecOn with
  | nil => rfl
  | append_singleton l v ih =>
      rw [HeadLayout.encSyms_snoc]
      simp only [List.length_append, List.length_cons, List.length_replicate,
        List.length_nil, List.sum_append, List.sum_cons, List.sum_nil, ih]
      omega

/-- `encodable.size` of a `List Nat` is `sum + length`. -/
theorem list_nat_size_eq (l : List Nat) : encodable.size l = l.sum + l.length := by
  show l.foldl (fun acc x => acc + encodable.size x + 1) 0 = _
  have h : ∀ (m : List Nat) (a : Nat),
      m.foldl (fun acc x => acc + encodable.size x + 1) a = a + m.sum + m.length := by
    intro m
    induction m with
    | nil => intro a; simp
    | cons y ys ih =>
        intro a
        rw [List.foldl_cons, ih]
        show a + encodable.size y + 1 + ys.sum + ys.length = a + (y + ys.sum) + (ys.length + 1)
        have : encodable.size y = y := rfl
        omega
  simpa using h l 0

/-- The item stream costs at most twice the list's own `encodable.size`. -/
theorem encSyms_length_le_size (l : List Nat) :
    (HeadLayout.encSyms l).length ≤ 2 * encodable.size l := by
  rw [encSyms_length, list_nat_size_eq]; omega

/-! ### The machine stream is linear in the machine size

**The additive `+ 3` is forced.** The bound `size (flattenTM M) ≤ 3 * size M` is
false: the trivial machine (`sig = tapes = states = start = 0`,
`halt = trans = []`) has `size M = 1` but `flattenTM M = [0,0,0,0,0,0]`, whose
`encodable.size` is `6`. `flattenTM` always writes six header cells, and the
header of a machine of size `1` cannot be paid for multiplicatively. The bound
below is TIGHT at that machine (`6 = 3·1 + 3`) and at
`trans = [⟨0,[],0,[],[]⟩]` (`12 = 3·3 + 3`). -/

private theorem nat_size_append (a b : List Nat) :
    encodable.size (a ++ b) = encodable.size a + encodable.size b := by
  rw [list_nat_size_eq, list_nat_size_eq, list_nat_size_eq, List.sum_append,
    List.length_append]
  omega

/-- `encodable.size` of a list, as the sum of its elements' charges. -/
private theorem list_size_map_sum {α : Type} [encodable α] (l : List α) :
    encodable.size l = (l.map (fun x => encodable.size x + 1)).sum := by
  show l.foldl (fun acc x => acc + encodable.size x + 1) 0 = _
  have h : ∀ (m : List α) (a : Nat),
      m.foldl (fun acc x => acc + encodable.size x + 1) a
        = a + (m.map (fun x => encodable.size x + 1)).sum := by
    intro m
    induction m with
    | nil => intro a; simp
    | cons y ys ih =>
        intro a
        rw [List.foldl_cons, ih]
        simp only [List.map_cons, List.sum_cons]
        omega
  simpa using h l 0

private theorem list_size_cons {α : Type} [encodable α] (a : α) (l : List α) :
    encodable.size (a :: l) = encodable.size a + 1 + encodable.size l := by
  rw [list_size_map_sum (a :: l), list_size_map_sum l]
  simp only [List.map_cons, List.sum_cons]

private theorem nat_size_flatMap {α : Type} (f : α → List Nat) (l : List α) :
    encodable.size (l.flatMap f) = (l.map (fun a => encodable.size (f a))).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      rw [List.flatMap_cons, nat_size_append, ih]
      simp only [List.map_cons, List.sum_cons]

/-- One `Option Nat` costs at most twice its charge, *including* its own item
slot — the shape the entry bound needs. -/
private theorem opts_size_le : ∀ l : List (Option Nat),
    encodable.size (S1Parse.optsFlat l) + l.length ≤ 2 * encodable.size l
  | [] => by exact Nat.zero_le _
  | o :: l => by
      have ih := opts_size_le l
      have hflat : S1Parse.optsFlat (o :: l)
          = HeadLayout.encOptN o ++ S1Parse.optsFlat l := List.flatMap_cons ..
      have hb : encodable.size (HeadLayout.encOptN o) + 1
          ≤ 2 * (encodable.size o + 1) := by
        cases o with
        | none =>
            show encodable.size ([0] : List Nat) + 1 ≤ 2 * (0 + 1)
            rw [list_nat_size_eq]; simp
        | some v =>
            have hv : encodable.size (some v : Option Nat) = v + 1 := rfl
            show encodable.size ([1, v] : List Nat) + 1 ≤ _
            rw [list_nat_size_eq, hv]; simp; omega
      rw [hflat, nat_size_append, list_size_cons, List.length_cons]
      omega

private theorem moves_size_le : ∀ l : List TMMove,
    encodable.size (l.map HeadLayout.encMoveN) + l.length ≤ 2 * encodable.size l
  | [] => by exact Nat.zero_le _
  | m :: l => by
      have ih := moves_size_le l
      have hm : encodable.size (m :: l) = 2 + encodable.size l := by
        rw [list_size_cons]; cases m <;> rfl
      have hs : encodable.size ((m :: l).map HeadLayout.encMoveN)
          = HeadLayout.encMoveN m + 1 + encodable.size (l.map HeadLayout.encMoveN) := by
        rw [List.map_cons, list_size_cons]; rfl
      have hle : HeadLayout.encMoveN m ≤ 2 := by cases m <;> decide
      rw [hs, hm, List.length_cons]
      omega

private theorem halt_size_le : ∀ l : List Bool,
    encodable.size (l.map (fun b => if b then 1 else 0)) + l.length
      ≤ 2 * encodable.size l
  | [] => by exact Nat.zero_le _
  | b :: l => by
      have ih := halt_size_le l
      have hs : encodable.size ((b :: l).map (fun b => if b then 1 else 0))
          = (if b then 1 else 0) + 1
            + encodable.size (l.map (fun b => if b then 1 else 0)) := by
        rw [List.map_cons, list_size_cons]; rfl
      have hm : encodable.size (b :: l) = (if b then 1 else 0) + 1 + encodable.size l := by
        rw [list_size_cons]; cases b <;> rfl
      rw [hs, hm, List.length_cons]
      cases b <;> simp <;> omega

private theorem entry_size_le (e : FlatTMTransEntry) :
    encodable.size (HeadLayout.flattenEntry e) ≤ 2 * encodable.size e + 3 := by
  have h1 := opts_size_le e.src_tape_vals
  have h2 := opts_size_le e.dst_write_vals
  have h3 := moves_size_le e.move_dirs
  have hsz : encodable.size e
      = encodable.size e.src_state + encodable.size e.src_tape_vals
        + encodable.size e.dst_state + encodable.size e.dst_write_vals
        + encodable.size e.move_dirs + 1 := rfl
  have hst : encodable.size e.src_state = e.src_state := rfl
  have hdt : encodable.size e.dst_state = e.dst_state := rfl
  have hA : encodable.size ([e.src_state, e.src_tape_vals.length] : List Nat)
      = e.src_state + e.src_tape_vals.length + 2 := by
    rw [list_nat_size_eq]; simp
  have hB : encodable.size ([e.dst_state, e.dst_write_vals.length] : List Nat)
      = e.dst_state + e.dst_write_vals.length + 2 := by
    rw [list_nat_size_eq]; simp
  have hC : encodable.size ([e.move_dirs.length] : List Nat)
      = e.move_dirs.length + 1 := by
    rw [list_nat_size_eq]; simp
  rw [S1Parse.flattenEntry_eq, nat_size_append, nat_size_append, nat_size_append,
    nat_size_append, nat_size_append, hA, hB, hC]
  omega

private theorem length_eq_sum_ones {α : Type} (l : List α) :
    l.length = (l.map (fun _ => 1)).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.map_cons, List.sum_cons, List.length_cons]; omega

private theorem mul_sum_map {α : Type} (c : Nat) (f : α → Nat) (l : List α) :
    c * (l.map f).sum = (l.map (fun a => c * f a)).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, Nat.mul_add, ih]

private theorem trans_sum_le : ∀ l : List FlatTMTransEntry,
    (l.map (fun e => encodable.size (HeadLayout.flattenEntry e))).sum
        + (l.map (fun _ : FlatTMTransEntry => 1)).sum
      ≤ (l.map (fun e => 3 * (encodable.size e + 1))).sum
  | [] => by simp
  | a :: l => by
      have ih := trans_sum_le l
      have ha := entry_size_le a
      have hge : 1 ≤ encodable.size a := by
        show 1 ≤ encodable.size a.src_state + _ + _ + _ + _ + 1
        omega
      simp only [List.map_cons, List.sum_cons]
      omega

/-- **The flattened machine stream is linear in the machine's
`encodable.size`** — with a forced additive constant, see the section note. -/
theorem flattenTM_size_le (M : FlatTM) :
    encodable.size (HeadLayout.flattenTM M) ≤ 3 * encodable.size M + 3 := by
  have hH := halt_size_le M.halt
  have hT : encodable.size (S1Parse.transFlat M) + M.trans.length
      ≤ 3 * encodable.size M.trans := by
    unfold S1Parse.transFlat
    rw [nat_size_flatMap, list_size_map_sum M.trans, length_eq_sum_ones M.trans,
      mul_sum_map 3 (fun e => encodable.size e + 1) M.trans]
    exact trans_sum_le M.trans
  have hA : encodable.size ([M.sig, M.tapes, M.states, M.start, M.halt.length] : List Nat)
      = M.sig + M.tapes + M.states + M.start + M.halt.length + 5 := by
    rw [list_nat_size_eq]; simp; omega
  have hB : encodable.size ([M.trans.length] : List Nat) = M.trans.length + 1 := by
    rw [list_nat_size_eq]; simp
  have hM : encodable.size M
      = M.sig + M.tapes + M.states + M.start
        + encodable.size M.halt + encodable.size M.trans + 1 := rfl
  rw [S1Parse.flattenTM_eq, nat_size_append, nat_size_append, nat_size_append, hA, hB]
  omega

/-- The frozen head layout's total register content is linear in the instance
size — `encodeIn_size` with `encBound n = 8·n + 4`. -/
theorem headEncodeIn_size_le (x : flatTM × List Nat × Nat × Nat) :
    State.size (HeadLayout.headEncodeIn x) ≤ 8 * encodable.size x + 4 := by
  obtain ⟨M, s, maxSize, steps⟩ := x
  have hM := le_trans (encSyms_length_le_size (HeadLayout.flattenTM M))
    (Nat.mul_le_mul_left 2 (flattenTM_size_le M))
  have hs := encSyms_length_le_size s
  have hprod : encodable.size ((M, s, maxSize, steps) : flatTM × List Nat × Nat × Nat)
      = encodable.size M + (encodable.size s + (maxSize + steps + 1) + 1) + 1 := rfl
  show State.size [[], HeadLayout.encSyms (HeadLayout.flattenTM M),
    HeadLayout.encSyms s, List.replicate maxSize 1, List.replicate steps 1] ≤ _
  simp only [State.size, List.map_cons, List.map_nil, List.foldr_cons,
    List.foldr_nil, List.length_replicate, List.length_nil]
  omega

/-! ## The program

`S1Program.s1Program = stagePG ;; ifBit FLG yesBranch stageMNo` (`Reductions/S1Program.lean`),
with `S1Program.s1Program_computes`. -/

/-! ## The witness

**The witness is built in two steps.**
`s1WitnessOf` takes the program as a PARAMETER together with the three
contracts it has to meet, and `s1_reductionLang` is its instantiation at
`S1Program.s1Program`. Every downstream construction can be stated over `s1WitnessOf`,
so `#print axioms` keeps distinguishing "this interface is
validated" from "stage C is still a placeholder". Do not inline
`s1WitnessOf` back into `s1_reductionLang`.

The three contracts are exactly the remaining S1 obligations:

1. `hcomputes` — `S1Program.s1Program_computes` (open only through
   `stageC_run`);
2. `huses` — `S1Program.s1Program_usesBelow` (open only through
   `stageC_usesBelow`);
3. `hcost` — `S1CostBound`, discharged by `s1Program_costBound` below.
-/

private instance : Nonempty FlatTCC := ⟨S1Map.s1No⟩

/-! ### The cost contract: some polynomial works -/

/-- **The S1 cost contract**: some polynomial dominates *both* the program's
cost on the frozen head layout *and* the image's size. Bundling the two is what
makes the bound free — `PolyTimeComputableLang.output_size_le` is the only thing
that stops `cost_bound` from being raised at will. -/
def S1CostBound (c : Cmd) : Prop :=
  ∃ cb : Nat → Nat, inOPoly cb ∧ monotonic cb
    ∧ (∀ x : flatTM × List Nat × Nat × Nat,
        c.cost (HeadLayout.headEncodeIn x) ≤ cb (encodable.size x))
    ∧ (∀ x : flatTM × List Nat × Nat × Nat,
        encodable.size (S1Map.s1Map x) ≤ cb (encodable.size x))

private theorem inOPoly_pow_succ' (k : Nat) : inOPoly (fun n => (n + 1) ^ k) := by
  refine ⟨k, 2 ^ k, 1, ?_⟩
  intro n hn
  calc (n + 1) ^ k ≤ (2 * n) ^ k := Nat.pow_le_pow_left (by omega) k
    _ = 2 ^ k * n ^ k := by rw [Nat.mul_pow]

/-- **The cost ladder's entry point.** A structural cost bound — no
constants, no register table, no stage-by-stage accounting — plus the already
proven `headEncodeIn_size_le` discharges the whole cost contract. The witness's
`cost_bound` becomes `S1Map.s1Bound + K·8^(D+1)·(n+1)^(D+1)`, which still
dominates `S1Map.s1Map_size_le` by construction. -/
theorem s1CostBound_of_costLeSize (c : Cmd)
    (h : ∃ K D : Nat, ∀ (s : State) (n : Nat),
      State.size s ≤ n → c.cost s ≤ K * (n + 1) ^ (D + 1)) : S1CostBound c := by
  obtain ⟨K, D, hb⟩ := h
  refine ⟨fun n => S1Map.s1Bound n + K * 8 ^ (D + 1) * (n + 1) ^ (D + 1),
    inOPoly_add S1Map.s1Bound_poly
      (inOPoly_mul (inOPoly_const (K * 8 ^ (D + 1))) (inOPoly_pow_succ' (D + 1))),
    fun a b hab => Nat.add_le_add (S1Map.s1Bound_mono a b hab)
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)),
    fun x => ?_, fun x => Nat.le_add_right_of_le (S1Map.s1Map_size_le x)⟩
  have hcost := hb (HeadLayout.headEncodeIn x) (8 * encodable.size x + 4)
    (headEncodeIn_size_le x)
  have hpow : (8 * encodable.size x + 4 + 1) ^ (D + 1)
      ≤ 8 ^ (D + 1) * (encodable.size x + 1) ^ (D + 1) := by
    calc (8 * encodable.size x + 4 + 1) ^ (D + 1)
        ≤ (8 * (encodable.size x + 1)) ^ (D + 1) := Nat.pow_le_pow_left (by omega) _
      _ = 8 ^ (D + 1) * (encodable.size x + 1) ^ (D + 1) := by rw [Nat.mul_pow]
  refine le_trans hcost ?_
  show K * (8 * encodable.size x + 4 + 1) ^ (D + 1)
      ≤ S1Map.s1Bound (encodable.size x)
        + K * 8 ^ (D + 1) * (encodable.size x + 1) ^ (D + 1)
  have hstep : K * (8 * encodable.size x + 4 + 1) ^ (D + 1)
      ≤ K * 8 ^ (D + 1) * (encodable.size x + 1) ^ (D + 1) := by
    calc K * (8 * encodable.size x + 4 + 1) ^ (D + 1)
        ≤ K * (8 ^ (D + 1) * (encodable.size x + 1) ^ (D + 1)) :=
          Nat.mul_le_mul_left _ hpow
      _ = K * 8 ^ (D + 1) * (encodable.size x + 1) ^ (D + 1) := by ring
  omega

/-- **The S1 free reduction witness, over an arbitrary program meeting the
three S1 contracts.** Every other field is discharged from a proven lemma of
this file / `S1Map`. -/
noncomputable def s1WitnessOf (c : Cmd)
    (hcomputes : ∀ x : flatTM × List Nat × Nat × Nat,
      s1Extract (c.eval (HeadLayout.headEncodeIn x)) = s1Key (S1Map.s1Map x))
    (huses : Cmd.UsesBelow c s1RegBound)
    (hcost : S1CostBound c) :
    PolyTimeComputableLang S1Map.s1Map where
  c := c
  encodeIn := HeadLayout.headEncodeIn
  decodeOut := fun s => Function.invFun s1Key (s1Extract s)
  -- The cost ceiling: the card stream dominates, `Θ(|trans|·|Σ|⁴)` blocks of
  -- unary cells, each emitted by a quadratic-in-its-length loop. Degree 10
  -- matches `S1Map.s1Bound` (the output-size ceiling) with room to spare;
  -- tighten only if the built program refuses it.
  cost_bound := hcost.choose
  cost_bound_poly := hcost.choose_spec.1
  cost_bound_mono := hcost.choose_spec.2.1
  encBound := fun n => 8 * n + 4
  encBound_poly :=
    inOPoly_add (inOPoly_mul (inOPoly_const 8) inOPoly_id) (inOPoly_const 4)
  encBound_mono := fun a b h => Nat.add_le_add_right (Nat.mul_le_mul_left 8 h) 4
  encodeIn_size := headEncodeIn_size_le
  computes := fun x => by
    rw [hcomputes x]
    exact Function.leftInverse_invFun s1Key_injective _
  cost_le := hcost.choose_spec.2.2.1
  output_size_le := hcost.choose_spec.2.2.2
  enc_bit := HeadLayout.headEncodeIn_bitState
  regBound := s1RegBound
  usesBelow := huses
  width_le := fun x => by
    obtain ⟨M, s, maxSize, steps⟩ := x
    show (HeadLayout.headEncodeIn (M, s, maxSize, steps)).length ≤ s1RegBound
    simp [HeadLayout.headEncodeIn, S1Program.s1RegBound]
  decode_agree := fun x m => by
    have hagree : AgreeBelow s1RegBound
        (HeadLayout.headEncodeIn x ++ List.replicate m []) (HeadLayout.headEncodeIn x) :=
      fun r _ => State.get_append_replicate_nil _ _ _
    have h := Cmd.eval_agree c s1RegBound huses hagree
    show Function.invFun s1Key (s1Extract _) = Function.invFun s1Key (s1Extract _)
    unfold S1Program.s1Extract
    rw [h SIGMA (by decide), h INIT (by decide), h CARDS (by decide),
      h FINAL (by decide), h STEPS (by decide)]

/-- The register set the analysis starts from: every register of the frame. -/
def costRegs : Nat := 2 ^ 60 - 1

/-! ## The cost certificate

`Cmd.chk` (`Lang/CostGrow.lean`) is a decidable pass over the syntax of a program whose
success certifies the polynomial cost bound `Cmd.CapCost`. Running it on `s1Program` in one
kernel computation is too expensive: the program has about `5 · 10^5` nodes, because each of
the three kind levels of the prelude family copies its continuation seven times. The
certificate is therefore assembled from pieces with `CmdH` (`Lang/CostGrowHole.lean`): the
pass on the kind nest is expressed through the pass on its pieces at the masks with which
they are reached, those values are tabulated (`tbl3`, `tbl2`, `tbl1`) and each entry is
checked by the kernel on the corresponding piece. The tables were obtained by evaluating
the pass; the kernel checks every entry. -/

open S1Prelude S1Emit

def pSegH (kvR stR paR : Var) (klit : Nat) (kvSrcs : List Var) (star : Bool)
    (paSrcs : List Var) : CmdH :=
  .seq (.ofCmd (loadVal EK1 kvR klit kvSrcs)) (.seq (.ofCmd (setFlag stR star))
    (.seq (.ofCmd (loadVal EK1 paR 0 paSrcs)) .hole))

def pKindCmdH (kvR stR paR kcR : Var) : CmdH :=
  .seq (pSegH kvR stR paR 0 [] false [PBV]) (
  .seq (pSegH kvR stR paR 1 [] false [S1Parse.PSIG]) (
  .seq (pSegH kvR stR paR 2 [] true []) (
  .seq (pSegH kvR stR paR 3 [] true [PHB]) (
  .seq (pSegH kvR stR paR 4 [] false [PHB, S1Parse.PSIG]) (
  .seq (.forBnd kcR S1Parse.PSIG (pSegH kvR stR paR 5 [kcR] false [kcR]))
       (.forBnd kcR S1Parse.PSIG (pSegH kvR stR paR 5 [S1Parse.PSIG, kcR] false [PHB, kcR])))))))

theorem pSegH_fill (kvR stR paR : Var) (klit : Nat) (kvSrcs : List Var) (star : Bool)
    (paSrcs : List Var) (next : Cmd) :
    (pSegH kvR stR paR klit kvSrcs star paSrcs).fill next
      = pSeg kvR stR paR klit kvSrcs star paSrcs next := by
  simp [pSegH, pSeg, CmdH.fill, CmdH.fill_ofCmd]

theorem pKindCmdH_fill (kvR stR paR kcR : Var) (next : Cmd) :
    (pKindCmdH kvR stR paR kcR).fill next = pKindCmd kvR stR paR kcR next := by
  simp [pKindCmdH, pKindCmd, CmdH.fill, pSegH_fill]

def K3 : Cmd := pKindCmd PKV3 PST3 PPA3 PKC3 resNest
def K2 : Cmd := pKindCmd PKV2 PST2 PPA2 PKC2 K3

theorem K2_eq : K2 = (pKindCmdH PKV2 PST2 PPA2 PKC2).fill K3 := (pKindCmdH_fill _ _ _ _ _).symm
theorem kindNest_eq : kindNest = (pKindCmdH PKV1 PST1 PPA1 PKC1).fill K2 := (pKindCmdH_fill _ _ _ _ _).symm

theorem K3_ngm : K3.ngm = 70664954314752 := by decide +kernel
theorem K2_ngm : K2.ngm = 70664962179072 := by
  rw [K2_eq, CmdH.ngm_fill, K3_ngm]; decide +kernel
theorem kindNest_ngm : kindNest.ngm = 70664962670592 := by
  rw [kindNest_eq, CmdH.ngm_fill, K2_ngm]; decide +kernel

theorem K3_chk₁ : Cmd.chk 1152851116732448767 K3 = (true, 1152851118611496959, 0) := by decide +kernel
theorem K3_chk₂ : Cmd.chk 1152851118611496959 K3 = (true, 1152851118611496959, 0) := by decide +kernel
theorem K3_chk₃ : Cmd.chk 1152850839652532223 K3 = (true, 1152851118615691263, 0) := by decide +kernel
theorem K3_chk₄ : Cmd.chk 1152850839648337919 K3 = (true, 1152851118611496959, 0) := by decide +kernel

def tbl3 (m : Nat) : Bool × Nat × Nat :=
  if m = 1152851116732448767 then (true, 1152851118611496959, 0)
  else if m = 1152851118611496959 then (true, 1152851118611496959, 0)
  else if m = 1152850839652532223 then (true, 1152851118615691263, 0)
  else if m = 1152850839648337919 then (true, 1152851118611496959, 0)
  else Cmd.chk m K3

theorem tbl3_eq : (fun m => Cmd.chk m K3) = tbl3 := by
  funext m
  unfold tbl3
  split_ifs with h1 h2 h3 h4
  · subst h1; exact K3_chk₁
  · subst h2; exact K3_chk₂
  · subst h3; exact K3_chk₃
  · subst h4; exact K3_chk₄
  · rfl

theorem K2_chk_of (m : Nat) :
    Cmd.chk m K2 = (pKindCmdH PKV2 PST2 PPA2 PKC2).chkH tbl3 70664954314752 m := by
  rw [K2_eq, CmdH.chk_fill, K3_ngm, tbl3_eq]

theorem K2_chk₁ : Cmd.chk 1152851116732448767 K2 = (true, 1152851118611496959, 0) := by
  rw [K2_chk_of]; decide +kernel
theorem K2_chk₂ : Cmd.chk 1152851118611496959 K2 = (true, 1152851118611496959, 0) := by
  rw [K2_chk_of]; decide +kernel
theorem K2_chk₃ : Cmd.chk 1152850839644667903 K2 = (true, 1152851118611496959, 0) := by
  rw [K2_chk_of]; decide +kernel

def tbl2 (m : Nat) : Bool × Nat × Nat :=
  if m = 1152851116732448767 then (true, 1152851118611496959, 0)
  else if m = 1152851118611496959 then (true, 1152851118611496959, 0)
  else if m = 1152850839644667903 then (true, 1152851118611496959, 0)
  else Cmd.chk m K2

theorem tbl2_eq : (fun m => Cmd.chk m K2) = tbl2 := by
  funext m
  unfold tbl2
  split_ifs with h1 h2 h3
  · subst h1; exact K2_chk₁
  · subst h2; exact K2_chk₂
  · subst h3; exact K2_chk₃
  · rfl

theorem kindNest_chk : Cmd.chk 1152851116732383231 kindNest = (true, 1152851118611496959, 0) := by
  rw [kindNest_eq, CmdH.chk_fill, K2_ngm, tbl2_eq]
  decide +kernel

def tbl1 (m : Nat) : Bool × Nat × Nat :=
  if m = 1152851116732383231 then (true, 1152851118611496959, 0) else Cmd.chk m kindNest

theorem tbl1_eq : (fun m => Cmd.chk m kindNest) = tbl1 := by
  funext m
  unfold tbl1
  split_ifs with h1
  · subst h1; exact kindNest_chk
  · rfl

def progH : CmdH :=
  .seq (.ofCmd S1Parse.stagePG)
    (.ifBit S1Parse.FLG
      (.seq (.ofCmd S1Emit.stageSig)
        (.seq (.ofCmd S1Emit.stageInit)
          (.seq (.seq (.ofCmd S1CardEmit.cFive)
              (.seq (.ofCmd S1Step.stepFam) (.seq (.ofCmd S1Prelude.pPre) .hole)))
            (.seq (.ofCmd S1Emit.stageFin) (.ofCmd S1Program.stageMYes)))))
      (.ofCmd S1Cards.stageMNo))

theorem progH_fill : progH.fill kindNest = S1Program.s1Program := by
  simp [progH, CmdH.fill, CmdH.fill_ofCmd, S1Program.s1Program, S1Program.yesBranch,
    S1Program.ySuf1, S1Program.ySuf2, S1Program.ySuf3, S1Program.stageC, S1Prelude.cPrelude]

theorem s1Program_chk : (S1Program.s1Program.chk costRegs).1 = true := by
  rw [← progH_fill, CmdH.chk_fill, kindNest_ngm, tbl1_eq]
  decide +kernel

/-- The polynomial cost bound of the reduction program. -/
theorem s1Program_costLeSize : ∃ K D : Nat, ∀ (s : State) (n : Nat),
    State.size s ≤ n → S1Program.s1Program.cost s ≤ K * (n + 1) ^ (D + 1) :=
  Cmd.costLeSize_of_chk S1Program.s1Program costRegs s1Program_chk

/-- The cost contract at the real program. -/
theorem s1Program_costBound : S1CostBound S1Program.s1Program :=
  s1CostBound_of_costLeSize _ s1Program_costLeSize

end S1Witness
