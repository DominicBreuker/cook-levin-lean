/-! # WORK IN PROGRESS — `map`-over-lists witness (NOT built, NOT verified end-to-end)

Parked reference for the next agent (see `CookLevin/HANDOFF.md`). This builds
`PolyTimeComputableLang' (List.map f : List Nat → List Nat)` from a witness for
`f : Nat → Nat`, using the `forBnd` loop toolkit in `Lang/Frame.lean`.

STATUS at hand-off:
  * `mapInv_step` (loop eval invariant step) — PROVEN sorry-free.
  * `mapBody_cost_le` (loop per-iteration cost step) — PROVEN sorry-free.
  * `mapNat_outsize` (output size bound) — PROVEN sorry-free.
  * `PolyTimeComputableLang'.mapNatList` — assembly drafted; `normalizes`/`cost_le`
    were mid-debug. The `Var`-typed `omega` calls in the high-register branch of
    `normalizes` were just replaced by `Nat.lt_of_le_of_ne` / `Nat.ne_of_gt`
    chains, and the `cost_le` arithmetic (`hmul`) still needs the `Nat.mul_le_mul`
    tweak described in HANDOFF. NOT re-verified after the last edit.

This file lives under `parked/` so it is NOT compiled by `lake build`. Move it
into `Lang/PolyTime.lean` only once it is verified sorry-free and axiom-clean.
-/
import Complexity.Lang.PolyTime
open Complexity.Lang
set_option autoImplicit false
namespace Complexity.Lang

variable {f : Nat → Nat}

private def mapBody (W : PolyTimeComputableLang' f) : Cmd :=
  Cmd.op (Op.head 0 W.regBound) ;;
  Cmd.op (Op.tail W.regBound W.regBound) ;;
  W.c ;;
  Cmd.op (Op.concat (W.regBound + 1) (W.regBound + 1) 0)

private def mapInv (W : PolyTimeComputableLang' f) (xs : List Nat) (i : Nat) (st : State) : Prop :=
  st.get W.regBound = xs.drop i ∧ st.get (W.regBound + 1) = (xs.take i).map f
    ∧ ∀ r, 1 ≤ r → r < W.regBound → st.get r = []

private theorem mapBody_usesBelow (W : PolyTimeComputableLang' f) :
    Cmd.UsesBelow (mapBody W) (W.regBound + 2) := by
  have hW : Cmd.UsesBelow W.c (W.regBound + 2) := Cmd.UsesBelow_mono (by omega) W.usesBelow
  have e0 : (0 : Nat) < W.regBound + 2 := by omega
  have ek : W.regBound < W.regBound + 2 := by omega
  have ek1 : W.regBound + 1 < W.regBound + 2 := by omega
  exact ⟨⟨e0, ek⟩, ⟨ek, ek⟩, hW, ek1, ek1, e0⟩

private theorem mapInv_step (W : PolyTimeComputableLang' f) (xs : List Nat) (i : Nat) (st : State)
    (hi : i < xs.length) (hM : mapInv W xs i st) :
    mapInv W xs (i + 1) ((mapBody W).eval (st.set (W.regBound + 2) (List.replicate i 1))) := by
  obtain ⟨hrem, hout, hblank⟩ := hM
  have hk : 0 < W.regBound := Cmd.UsesBelow_pos W.usesBelow
  set st' := st.set (W.regBound + 2) (List.replicate i 1) with hst'
  obtain ⟨a, t, hd⟩ : ∃ a t, xs.drop i = a :: t := by
    rcases hxd : xs.drop i with _ | ⟨a, t⟩
    · exact absurd (show xs.length - i = 0 by rw [← List.length_drop, hxd]; rfl) (by omega)
    · exact ⟨a, t, rfl⟩
  have ht : xs.drop (i + 1) = t := by rw [← List.tail_drop, hd]; rfl
  have g'k : st'.get W.regBound = a :: t := by
    rw [hst', State.get_set_ne _ _ _ _ (by omega : W.regBound ≠ W.regBound + 2), hrem, hd]
  have g'k1 : st'.get (W.regBound + 1) = (xs.take i).map f := by
    rw [hst', State.get_set_ne _ _ _ _ (by omega : W.regBound + 1 ≠ W.regBound + 2), hout]
  have g'blank : ∀ r, 1 ≤ r → r < W.regBound → st'.get r = [] := by
    intro r hr1 hr2
    rw [hst', State.get_set_ne _ _ _ _ (Nat.ne_of_lt (Nat.lt_succ_of_lt (Nat.lt_succ_of_lt hr2)))]
    exact hblank r hr1 hr2
  show mapInv W xs (i + 1)
      ((Cmd.op (Op.head 0 W.regBound) ;; Cmd.op (Op.tail W.regBound W.regBound) ;; W.c ;;
        Cmd.op (Op.concat (W.regBound + 1) (W.regBound + 1) 0)).eval st')
  rw [Cmd.eval_seq, Cmd.eval_seq, Cmd.eval_seq]
  have ea : (Cmd.op (Op.head 0 W.regBound)).eval st' = st'.set 0 [a] := by
    show st'.set 0 (match st'.get W.regBound with | [] => [] | x :: _ => [x]) = st'.set 0 [a]
    rw [g'k]
  rw [ea]
  have eb : (Cmd.op (Op.tail W.regBound W.regBound)).eval (st'.set 0 [a])
      = (st'.set 0 [a]).set W.regBound t := by
    show (st'.set 0 [a]).set W.regBound (((st'.set 0 [a]).get W.regBound)).tail
        = (st'.set 0 [a]).set W.regBound t
    rw [State.get_set_ne _ _ _ _ (by omega : W.regBound ≠ 0), g'k, List.tail_cons]
  rw [eb]
  set sb := (st'.set 0 [a]).set W.regBound t with hsb
  have hag : AgreeBelow W.regBound (LangEncodable.encodeState (a : Nat)) sb := by
    intro r hr
    by_cases hr0 : r = 0
    · subst hr0
      rw [hsb, State.get_set_ne _ _ _ _ (by omega : (0:Nat) ≠ W.regBound), State.get_set_eq]; rfl
    · have hr1 : 1 ≤ r := Nat.pos_of_ne_zero hr0
      rw [hsb, State.get_set_ne _ _ _ _ (Nat.ne_of_lt hr),
        State.get_set_ne _ _ _ _ hr0, g'blank r hr1 hr,
        LangEncodable.encodeState_get_pos (a : Nat) hr1]
  set sc := W.c.eval sb with hsc
  have sc0 : sc.get 0 = [f a] := by
    rw [hsc, W.eval_get_of_agree (a : Nat) hag hk]; rfl
  have sck : sc.get W.regBound = t := by
    rw [hsc, W.eval_frame sb (le_refl _), hsb, State.get_set_eq]
  have sck1 : sc.get (W.regBound + 1) = (xs.take i).map f := by
    rw [hsc, W.eval_frame sb (by omega : W.regBound ≤ W.regBound + 1), hsb,
      State.get_set_ne _ _ _ _ (by omega : W.regBound + 1 ≠ W.regBound),
      State.get_set_ne _ _ _ _ (by omega : W.regBound + 1 ≠ 0), g'k1]
  have scblank : ∀ r, 1 ≤ r → r < W.regBound → sc.get r = [] := by
    intro r hr1 hr2
    rw [hsc, W.eval_get_of_agree (a : Nat) hag hr2, LangEncodable.encodeState_get_pos (f a : Nat) hr1]
  show mapInv W xs (i + 1) ((Cmd.op (Op.concat (W.regBound + 1) (W.regBound + 1) 0)).eval sc)
  have ed : (Cmd.op (Op.concat (W.regBound + 1) (W.regBound + 1) 0)).eval sc
      = sc.set (W.regBound + 1) (sc.get (W.regBound + 1) ++ sc.get 0) := rfl
  rw [ed]
  refine ⟨?_, ?_, ?_⟩
  · rw [State.get_set_ne _ _ _ _ (by omega : W.regBound ≠ W.regBound + 1), sck, ht]
  · rw [State.get_set_eq, sck1, sc0]
    have htk : xs.take (i + 1) = xs.take i ++ [a] := by
      rw [List.take_add, hd]; simp
    rw [htk, List.map_append]; simp
  · intro r hr1 hr2
    rw [State.get_set_ne _ _ _ _ (Nat.ne_of_lt (Nat.lt_succ_of_lt hr2))]
    exact scblank r hr1 hr2

private theorem mapBody_cost_le (W : PolyTimeComputableLang' f) (xs : List Nat) (i : Nat) (st : State)
    (hi : i < xs.length) (hM : mapInv W xs i st) :
    (mapBody W).cost (st.set (W.regBound + 2) (List.replicate i 1))
      ≤ 6 + W.cost_bound (encodable.size xs) := by
  obtain ⟨hrem, hout, hblank⟩ := hM
  have hk : 0 < W.regBound := Cmd.UsesBelow_pos W.usesBelow
  set st' := st.set (W.regBound + 2) (List.replicate i 1) with hst'
  obtain ⟨a, t, hd⟩ : ∃ a t, xs.drop i = a :: t := by
    rcases hxd : xs.drop i with _ | ⟨a, t⟩
    · exact absurd (show xs.length - i = 0 by rw [← List.length_drop, hxd]; rfl) (by omega)
    · exact ⟨a, t, rfl⟩
  have g'k : st'.get W.regBound = a :: t := by
    rw [hst', State.get_set_ne _ _ _ _ (by omega : W.regBound ≠ W.regBound + 2), hrem, hd]
  have g'blank : ∀ r, 1 ≤ r → r < W.regBound → st'.get r = [] := by
    intro r hr1 hr2
    rw [hst', State.get_set_ne _ _ _ _ (Nat.ne_of_lt (Nat.lt_succ_of_lt (Nat.lt_succ_of_lt hr2)))]
    exact hblank r hr1 hr2
  have ea : (Cmd.op (Op.head 0 W.regBound)).eval st' = st'.set 0 [a] := by
    show st'.set 0 (match st'.get W.regBound with | [] => [] | x :: _ => [x]) = st'.set 0 [a]
    rw [g'k]
  have eb : (Cmd.op (Op.tail W.regBound W.regBound)).eval (st'.set 0 [a])
      = (st'.set 0 [a]).set W.regBound t := by
    show (st'.set 0 [a]).set W.regBound (((st'.set 0 [a]).get W.regBound)).tail
        = (st'.set 0 [a]).set W.regBound t
    rw [State.get_set_ne _ _ _ _ (by omega : W.regBound ≠ 0), g'k, List.tail_cons]
  set sb := (st'.set 0 [a]).set W.regBound t with hsb
  have hag : AgreeBelow W.regBound (LangEncodable.encodeState (a : Nat)) sb := by
    intro r hr
    by_cases hr0 : r = 0
    · subst hr0
      rw [hsb, State.get_set_ne _ _ _ _ (by omega : (0:Nat) ≠ W.regBound), State.get_set_eq]; rfl
    · have hr1 : 1 ≤ r := Nat.pos_of_ne_zero hr0
      rw [hsb, State.get_set_ne _ _ _ _ (Nat.ne_of_lt hr),
        State.get_set_ne _ _ _ _ hr0, g'blank r hr1 hr,
        LangEncodable.encodeState_get_pos (a : Nat) hr1]
  -- the element's size is bounded by the whole list's size
  have hsize_a : encodable.size a ≤ encodable.size xs := by
    have hsplit : xs = xs.take i ++ a :: t := by
      rw [← hd]; exact (List.take_append_drop i xs).symm
    have : encodable.size xs
        = encodable.size (xs.take i) + (encodable.size a + 1 + encodable.size t) := by
      conv_lhs => rw [hsplit]
      rw [encodable_size_list_append, encodable_size_list_cons]
    omega
  -- the body cost is `6 + W.c.cost sb`
  have hcost : (mapBody W).cost st' = 6 + W.c.cost sb := by
    show (Cmd.op (Op.head 0 W.regBound) ;; Cmd.op (Op.tail W.regBound W.regBound) ;; W.c ;;
          Cmd.op (Op.concat (W.regBound + 1) (W.regBound + 1) 0)).cost st' = 6 + W.c.cost sb
    rw [Cmd.cost_seq, Cmd.cost_seq, Cmd.cost_seq, ea, eb]
    simp only [Cmd.cost_op, Op.cost]
    omega
  rw [hcost, ← Cmd.cost_agree W.c W.regBound W.usesBelow hag]
  have h1 : W.c.cost (LangEncodable.encodeState (a : Nat)) ≤ W.cost_bound (encodable.size a) :=
    W.cost_le a
  have h2 : W.cost_bound (encodable.size a) ≤ W.cost_bound (encodable.size xs) :=
    W.cost_bound_mono _ _ hsize_a
  omega

/-- The output `List.map f xs` is polynomially size-bounded. -/
private theorem mapNat_outsize (W : PolyTimeComputableLang' f) :
    ∀ xs : List Nat,
      encodable.size (xs.map f) ≤ xs.length * (W.cost_bound (encodable.size xs) + 1)
  | [] => by simp [encodable.size]
  | x :: xs => by
      have ih := mapNat_outsize W xs
      have hsizes : encodable.size xs ≤ encodable.size (x :: xs) := by
        rw [encodable_size_list_cons]; omega
      have hsx : encodable.size x ≤ encodable.size (x :: xs) := by
        rw [encodable_size_list_cons]; omega
      have hfx : encodable.size (f x) ≤ W.cost_bound (encodable.size (x :: xs)) :=
        le_trans (W.output_size_le x) (W.cost_bound_mono _ _ hsx)
      have ih' : encodable.size (xs.map f)
          ≤ xs.length * (W.cost_bound (encodable.size (x :: xs)) + 1) :=
        le_trans ih (Nat.mul_le_mul_left _ (Nat.add_le_add_right (W.cost_bound_mono _ _ hsizes) 1))
      rw [List.map_cons, encodable_size_list_cons, List.length_cons, Nat.succ_mul]
      omega

/-- The full `map` program: stash the input in `REM = regBound`, init `OUT = regBound+1`
to `[]`, loop (`forBnd`) peeling/transforming/appending one element per step, then
copy `OUT` to register `0` and clear scratch. -/
def mapNatListCmd (W : PolyTimeComputableLang' f) : Cmd :=
  Cmd.op (Op.copy W.regBound 0) ;;
  Cmd.op (Op.clear (W.regBound + 1)) ;;
  Cmd.forBnd (W.regBound + 2) W.regBound (mapBody W) ;;
  Cmd.op (Op.copy 0 (W.regBound + 1)) ;;
  Cmd.op (Op.clear W.regBound) ;;
  Cmd.op (Op.clear (W.regBound + 1)) ;;
  Cmd.op (Op.clear (W.regBound + 2))

/-- **`map`: lists are mapped by a loop over the per-element witness.** Given a
canonical witness for `f : Nat → Nat`, builds one for `List.map f`. The first
loop-based layer program proved end-to-end with the `forBnd` toolkit. -/
def PolyTimeComputableLang'.mapNatList (W : PolyTimeComputableLang' f) :
    PolyTimeComputableLang' (List.map f : List Nat → List Nat) where
  c := mapNatListCmd W
  cost_bound := fun n => 13 + (n + 1) * (W.cost_bound n + 6)
  cost_bound_poly :=
    inOPoly_add (inOPoly_const 13)
      (inOPoly_mul (inOPoly_add inOPoly_id (inOPoly_const 1))
        (inOPoly_add W.cost_bound_poly (inOPoly_const 6)))
  cost_bound_mono := by
    intro a b hab
    have hcb : W.cost_bound a ≤ W.cost_bound b := W.cost_bound_mono _ _ hab
    have : (a + 1) * (W.cost_bound a + 6) ≤ (b + 1) * (W.cost_bound b + 6) :=
      Nat.mul_le_mul (by omega) (by omega)
    show 13 + (a + 1) * (W.cost_bound a + 6) ≤ 13 + (b + 1) * (W.cost_bound b + 6)
    omega
  normalizes := by
    intro xs r
    have hk : 0 < W.regBound := Cmd.UsesBelow_pos W.usesBelow
    -- input reads
    have hein0 : (LangEncodable.encodeState (xs : List Nat)).get 0 = xs := rfl
    -- the pre-loop state `s0`
    set ein := LangEncodable.encodeState (xs : List Nat) with hein
    have hc1 : (Cmd.op (Op.copy W.regBound 0)).eval ein = ein.set W.regBound xs := by
      show ein.set W.regBound (ein.get 0) = ein.set W.regBound xs
      rw [hein0]
    set s0 := (ein.set W.regBound xs).set (W.regBound + 1) [] with hs0
    have hs0k : s0.get W.regBound = xs := by
      rw [hs0, State.get_set_ne _ _ _ _ (by omega : W.regBound ≠ W.regBound + 1), State.get_set_eq]
    -- loop result
    set sL := Cmd.foldlState (mapBody W) (W.regBound + 2) (List.range xs.length) s0 with hsL
    have hinv0 : mapInv W xs 0 s0 := by
      refine ⟨by rw [hs0k]; rfl, ?_, ?_⟩
      · rw [hs0, State.get_set_eq]; rfl
      · intro r hr1 hr2
        rw [hs0, State.get_set_ne _ _ _ _ (Nat.ne_of_lt (Nat.lt_succ_of_lt hr2)),
          State.get_set_ne _ _ _ _ (Nat.ne_of_lt hr2), hein,
          LangEncodable.encodeState_get_pos (xs : List Nat) hr1]
    have hinv : mapInv W xs xs.length sL :=
      Cmd.foldlState_range_induct (mapBody W) (W.regBound + 2) xs.length s0 (mapInv W xs)
        hinv0 (fun i st hi hM => mapInv_step W xs i st hi hM)
    obtain ⟨hLrem, hLout, hLblank⟩ := hinv
    have hLk1 : sL.get (W.regBound + 1) = xs.map f := by rw [hLout, List.take_length]
    -- high registers preserved by the loop
    have hbodyUB : Cmd.UsesBelow (mapBody W) (W.regBound + 3) :=
      Cmd.UsesBelow_mono (by omega) (mapBody_usesBelow W)
    have hLframe : ∀ q, W.regBound + 3 ≤ q → sL.get q = s0.get q := by
      intro q hq
      exact Cmd.foldlState_frame (mapBody W) (W.regBound + 2) xs.length s0 (W.regBound + 3)
        (by omega) hbodyUB q hq
    have hloop : (Cmd.forBnd (W.regBound + 2) W.regBound (mapBody W)).eval s0 = sL := by
      rw [Cmd.eval_forBnd, hs0k]
    -- assemble the whole evaluation
    show State.get ((mapNatListCmd W).eval ein) r
        = State.get (LangEncodable.encodeState (List.map f xs)) r
    unfold mapNatListCmd
    rw [Cmd.eval_seq, Cmd.eval_seq, Cmd.eval_seq, Cmd.eval_seq, Cmd.eval_seq, Cmd.eval_seq,
      hc1]
    show State.get ((Cmd.op (Op.clear (W.regBound + 2))).eval ((Cmd.op (Op.clear (W.regBound + 1))).eval
      ((Cmd.op (Op.clear W.regBound)).eval ((Cmd.op (Op.copy 0 (W.regBound + 1))).eval
        ((Cmd.forBnd (W.regBound + 2) W.regBound (mapBody W)).eval
          ((Cmd.op (Op.clear (W.regBound + 1))).eval (ein.set W.regBound xs))))))) r = _
    rw [show (Cmd.op (Op.clear (W.regBound + 1))).eval (ein.set W.regBound xs) = s0 from rfl, hloop]
    -- now: clear(k+2) (clear(k+1) (clear k (copy 0 (k+1) sL)))
    rw [show (Cmd.op (Op.copy 0 (W.regBound + 1))).eval sL = sL.set 0 (xs.map f) by
        show sL.set 0 (sL.get (W.regBound + 1)) = sL.set 0 (xs.map f); rw [hLk1]]
    show State.get (((((sL.set 0 (xs.map f)).set W.regBound []).set (W.regBound + 1) []).set
      (W.regBound + 2) [])) r = State.get (LangEncodable.encodeState (List.map f xs)) r
    by_cases hr0 : r = 0
    · subst hr0
      rw [State.get_set_ne _ _ _ _ (by omega : (0:Nat) ≠ W.regBound + 2),
        State.get_set_ne _ _ _ _ (by omega : (0:Nat) ≠ W.regBound + 1),
        State.get_set_ne _ _ _ _ (by omega : (0:Nat) ≠ W.regBound),
        State.get_set_eq]
      rfl
    · have hr1 : 1 ≤ r := Nat.pos_of_ne_zero hr0
      rw [LangEncodable.encodeState_get_pos (List.map f xs) hr1]
      by_cases hrk2 : r = W.regBound + 2
      · subst hrk2; rw [State.get_set_eq]
      · rw [State.get_set_ne _ _ _ _ hrk2]
        by_cases hrk1 : r = W.regBound + 1
        · subst hrk1; rw [State.get_set_eq]
        · rw [State.get_set_ne _ _ _ _ hrk1]
          by_cases hrk : r = W.regBound
          · subst hrk; rw [State.get_set_eq]
          · rw [State.get_set_ne _ _ _ _ hrk, State.get_set_ne _ _ _ _ hr0]
            rcases Nat.lt_or_ge r W.regBound with hlt | hge
            · exact hLblank r hr1 hlt
            · have h1 : W.regBound + 1 ≤ r := Nat.lt_of_le_of_ne hge (Ne.symm hrk)
              have h2 : W.regBound + 2 ≤ r := Nat.lt_of_le_of_ne h1 (Ne.symm hrk1)
              have hge3 : W.regBound + 3 ≤ r := Nat.lt_of_le_of_ne h2 (Ne.symm hrk2)
              rw [hLframe r hge3, hs0,
                State.get_set_ne _ _ _ _
                  (Nat.ne_of_gt (Nat.lt_of_lt_of_le (by omega : W.regBound + 1 < W.regBound + 3) hge3)),
                State.get_set_ne _ _ _ _
                  (Nat.ne_of_gt (Nat.lt_of_lt_of_le (by omega : W.regBound < W.regBound + 3) hge3)),
                hein, LangEncodable.encodeState_get_pos (xs : List Nat) hr1]
  cost_le := by
    intro xs
    have hk : 0 < W.regBound := Cmd.UsesBelow_pos W.usesBelow
    have hein0 : (LangEncodable.encodeState (xs : List Nat)).get 0 = xs := rfl
    set ein := LangEncodable.encodeState (xs : List Nat) with hein
    have hc1 : (Cmd.op (Op.copy W.regBound 0)).eval ein = ein.set W.regBound xs := by
      show ein.set W.regBound (ein.get 0) = ein.set W.regBound xs; rw [hein0]
    set s0 := (ein.set W.regBound xs).set (W.regBound + 1) [] with hs0
    have hs0k : s0.get W.regBound = xs := by
      rw [hs0, State.get_set_ne _ _ _ _ (by omega : W.regBound ≠ W.regBound + 1), State.get_set_eq]
    have hinv0 : mapInv W xs 0 s0 := by
      refine ⟨by rw [hs0k]; rfl, ?_, ?_⟩
      · rw [hs0, State.get_set_eq]; rfl
      · intro r hr1 hr2
        rw [hs0, State.get_set_ne _ _ _ _ (Nat.ne_of_lt (Nat.lt_succ_of_lt hr2)),
          State.get_set_ne _ _ _ _ (Nat.ne_of_lt hr2), hein,
          LangEncodable.encodeState_get_pos (xs : List Nat) hr1]
    -- the loop's cost
    have hforcost : (Cmd.forBnd (W.regBound + 2) W.regBound (mapBody W)).cost s0
        ≤ 1 + xs.length * (6 + W.cost_bound (encodable.size xs)) := by
      have := Cmd.cost_forBnd_le (W.regBound + 2) W.regBound (mapBody W) s0
        (6 + W.cost_bound (encodable.size xs)) (mapInv W xs) hinv0
        (fun i st hi hM => mapInv_step W xs i st (by rw [hs0k] at hi; exact hi) hM)
        (fun i st hi hM => mapBody_cost_le W xs i st (by rw [hs0k] at hi; exact hi) hM)
      rw [hs0k] at this
      exact this
    have hlen : xs.length ≤ encodable.size xs := by
      have h : xs.length ≤ encodable.size xs := by
        induction xs with
        | nil => simp [encodable.size]
        | cons x xs ih => rw [encodable_size_list_cons, List.length_cons]; omega
      exact h
    -- total cost = 12 + forBnd cost
    show (mapNatListCmd W).cost ein ≤ 13 + (encodable.size xs + 1) * (W.cost_bound (encodable.size xs) + 6)
    have htotal : (mapNatListCmd W).cost ein
        = 12 + (Cmd.forBnd (W.regBound + 2) W.regBound (mapBody W)).cost s0 := by
      unfold mapNatListCmd
      rw [Cmd.cost_seq, Cmd.cost_seq, Cmd.cost_seq, Cmd.cost_seq, Cmd.cost_seq, Cmd.cost_seq,
        hc1, show (Cmd.op (Op.clear (W.regBound + 1))).eval (ein.set W.regBound xs) = s0 from rfl]
      simp only [Cmd.cost_op, Op.cost]
      omega
    rw [htotal]
    -- arithmetic: 12 + forBnd ≤ 13 + (size+1)*(cb+6)
    have hmul : xs.length * (6 + W.cost_bound (encodable.size xs))
        ≤ (encodable.size xs + 1) * (W.cost_bound (encodable.size xs) + 6) := by
      apply Nat.le_trans (Nat.mul_le_mul_right _ (Nat.le_succ_of_le hlen))
      rw [Nat.mul_comm 6 _] -- align summands; then both sides equal
      exact Nat.le_of_eq (by rw [Nat.add_comm (W.cost_bound (encodable.size xs)) 6])
    omega
  output_size_le := by
    intro xs
    have hlen : xs.length ≤ encodable.size xs := by
      induction xs with
      | nil => simp [encodable.size]
      | cons x xs ih => rw [encodable_size_list_cons, List.length_cons]; omega
    have hout := mapNat_outsize W xs
    have hmul : xs.length * (W.cost_bound (encodable.size xs) + 1)
        ≤ (encodable.size xs + 1) * (W.cost_bound (encodable.size xs) + 6) :=
      Nat.mul_le_mul (Nat.le_succ_of_le hlen) (by omega)
    show encodable.size (List.map f xs)
        ≤ 13 + (encodable.size xs + 1) * (W.cost_bound (encodable.size xs) + 6)
    omega
  regBound := W.regBound + 3
  usesBelow := by
    have hbodyUB : Cmd.UsesBelow (mapBody W) (W.regBound + 3) :=
      Cmd.UsesBelow_mono (by omega) (mapBody_usesBelow W)
    have e0 : (0 : Nat) < W.regBound + 3 := by omega
    have ek : W.regBound < W.regBound + 3 := by omega
    have ek1 : W.regBound + 1 < W.regBound + 3 := by omega
    have ek2 : W.regBound + 2 < W.regBound + 3 := by omega
    exact ⟨⟨ek, e0⟩, ek1, ⟨ek2, ek, hbodyUB⟩, ⟨e0, ek1⟩, ek, ek1, ek2⟩

#print axioms PolyTimeComputableLang'.mapNatList

end Complexity.Lang

