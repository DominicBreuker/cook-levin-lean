import CookLevin.Simulation.Cost
import CookLevin.Lang.HardnessStr

set_option autoImplicit false

/-! # Every language in NP has a verifier program

`inNP_inNPCmd`: a polynomial-time single-tape Turing-machine verifier (`inNP`,
`Basic/StringTM.lean`) is turned into a polynomial-cost verifier program (`inNPCmd`,
`Lang/HardnessStr.lean`). The program is `simTM` (`Simulation/Program.lean`): it checks the
certificate length and simulates the machine for a polynomial number of steps; its cost is
bounded by the polynomial `simBound` (`Simulation/Cost.lean`).
-/

namespace CookLevin.Sim

open CookLevin.Lang FrontPieces CookLevin.Lang.FrontWitness

/-! ## The total cost -/

/-- The cost bound of the main loop with budget `T` on inputs of total length `n`. -/
def loopBound (M : FlatTM) (T n : Nat) : Nat :=
  1 + T * ((loopBody M).flatK * (wid M * (n + 4 + T) + T + M.states + 2)) + T * T

/-- The cost bound of `simTM` on inputs of total length `n`. -/
def simBound (M : FlatTM) (acc a k b ct kt dt n : Nat) : Nat :=
  4 + lenBound a k b n n + timerBound ct kt dt n n + initBound (wid M) M.start n n
    + loopBound M (budget ct kt dt n) n + (3 * acc + M.states + 10)

theorem lenBound_mono (a k b : Nat) {mx mc n : Nat} (hx : mx ≤ n) (hc : mc ≤ n) :
    lenBound a k b mx mc ≤ lenBound a k b n n := by
  unfold lenBound; gcongr

theorem timerBound_mono (ct kt dt : Nat) {mx mc n : Nat} (hx : mx ≤ n) (hc : mc ≤ n) :
    timerBound ct kt dt mx mc ≤ timerBound ct kt dt n n := by
  unfold timerBound
  have h1 := tallyRegCost_mono hx
  have h2 := tallyRegCost_mono hc
  have h3 := monoUB_mono ct kt dt (mx + mc) (n + n) (by omega)
  omega

theorem initBound_mono (W q : Nat) {mx mc n : Nat} (hx : mx ≤ n) (hc : mc ≤ n) :
    initBound W q mx mc ≤ initBound W q n n := by
  unfold initBound bitBound; gcongr

theorem pairTape_length (x c : List Bool) : (pairTape x c).length = x.length + c.length + 4 := by
  simp [pairTape, symbolsOf]; omega

theorem simTM_cost (M : FlatTM) (hM : validFlatTM M) (h1 : M.tapes = 1)
    (acc a k b ct kt dt : Nat) (x c : List Bool) :
    (simTM M acc a k b ct kt dt).cost (inputState x c)
      ≤ simBound M acc a k b ct kt dt (x.length + c.length) := by
  set n := x.length + c.length with hn
  set s0 := inputState x c with hs0
  have hx0 : State.get s0 XO = bitsOf x := rfl
  have hc0 : State.get s0 CI = bitsOf c := rfl
  have hxl : (bitsOf x).length = x.length := by simp [bitsOf]
  have hcl : (bitsOf c).length = c.length := by simp [bitsOf]
  unfold simTM
  -- phase 1
  have L := lenCode_cost a k b s0
  rw [hx0, hc0, hxl, hcl] at L
  obtain ⟨-, l2⟩ := lenCode_run a k b s0
  set s1 := (lenCode a k b).eval s0 with hs1
  have hx1 : State.get s1 XO = bitsOf x := by rw [l2 _ (by decide), hx0]
  have hc1 : State.get s1 CI = bitsOf c := by rw [l2 _ (by decide), hc0]
  -- phase 2
  have Tm := timerCode_cost ct kt dt s1
  rw [hx1, hc1, hxl, hcl] at Tm
  obtain ⟨m1, m2⟩ := timerCode_run ct kt dt s1
  set s2 := (timerCode ct kt dt).eval s1 with hs2
  have hx2 : State.get s2 XO = bitsOf x := by rw [m2 _ (by decide), hx1]
  have hc2 : State.get s2 CI = bitsOf c := by rw [m2 _ (by decide), hc1]
  -- phase 3
  have I := initCode_cost M x c s2 hx2 hc2
  obtain ⟨i1, i2, i3⟩ := initCode_run M x c s2 hx2 hc2
  set s3 := (initCode M).eval s2 with hs3
  have hT3 : (State.get s3 TIMER).length = budget ct kt dt n := by
    rw [i3 _ (by decide), m1, hx1, hc1, hxl, hcl, List.length_replicate]
  -- phase 4
  have ML := mainLoop_cost M hM h1 _ s3 i1 i2 [] 0 (pairTape x c) rfl hM.1
  rw [hT3, pairTape_length] at ML
  have hR4 := mainLoop_run M hM h1 _ s3 i1
  rw [hT3] at hR4
  set s4 := (mainLoop M).eval s3 with hs4
  -- phase 5
  have V := verdict_cost acc s4
  obtain ⟨l', h', r', ht', -, -, hq'⟩ := iterate_growth M hM h1 (initFlatConfig M [pairTape x c])
    [] 0 (pairTape x c) rfl hM.1 (budget ct kt dt n)
  have hST := (repr_lengths M _ s4 hR4 l' h' r' ht').2.2.2.1
  rw [hST] at V
  -- assemble
  have hall := cost_seq_le L (cost_seq_le Tm (cost_seq_le I (cost_seq_le ML V)))
  refine hall.trans ?_
  have e1 := lenBound_mono a k b (show x.length ≤ n by omega) (show c.length ≤ n by omega)
  have e2 := timerBound_mono ct kt dt (show x.length ≤ n by omega) (show c.length ≤ n by omega)
  have e3 := initBound_mono (wid M) M.start (show x.length ≤ n by omega)
    (show c.length ≤ n by omega)
  unfold simBound loopBound
  have e4 : wid M * (x.length + c.length + 4 + budget ct kt dt n) + 0 + budget ct kt dt n
      + M.states + 1 + 1 = wid M * (n + 4 + budget ct kt dt n) + budget ct kt dt n
      + M.states + 2 := by rw [hn]; omega
  rw [e4] at ML ⊢
  omega

/-! ## The bound is a monotone polynomial -/

theorem inOPoly_pow' (k : Nat) : inOPoly (fun n => n ^ k) :=
  inOPoly_of_le (fun n => Nat.pow_le_pow_left (Nat.le_succ n) k) (inOPoly_pow_succ k)

theorem budget_poly (ct kt dt : Nat) : inOPoly (fun n => budget ct kt dt n) :=
  inOPoly_add (inOPoly_mul (inOPoly_const ct) (inOPoly_pow_succ kt)) (inOPoly_const dt)

theorem monoUB_double_poly (ct kt dt : Nat) : inOPoly (fun n => monoUB ct kt dt (n + n)) :=
  inOPoly_comp (f := fun n => n + n) (inOPoly_add inOPoly_id inOPoly_id) (monoUB_poly ct kt dt)

theorem lenBound_poly (a k b : Nat) : inOPoly (fun n => lenBound a k b n n) := by
  unfold lenBound
  have Y : inOPoly (fun n => a * n ^ k + b) :=
    inOPoly_add (inOPoly_mul (inOPoly_const a) (inOPoly_pow' k)) (inOPoly_const b)
  exact inOPoly_add (inOPoly_add (inOPoly_add (inOPoly_add (inOPoly_add (inOPoly_add
    (inOPoly_add (inOPoly_add (inOPoly_const 30) (inOPoly_mul (inOPoly_const 5) inOPoly_id))
      (inOPoly_mul inOPoly_id inOPoly_id)) (inOPoly_const _))
      (inOPoly_mul (inOPoly_const _) (inOPoly_pow_succ _))) (inOPoly_const _)) Y)
      (inOPoly_mul inOPoly_id (inOPoly_add Y (inOPoly_const 6))))
    (inOPoly_mul inOPoly_id inOPoly_id)

theorem timerBound_poly (ct kt dt : Nat) : inOPoly (fun n => timerBound ct kt dt n n) := by
  unfold timerBound
  exact inOPoly_add (inOPoly_add (inOPoly_add (inOPoly_const 2)
    (tallyRegCost_comp_poly inOPoly_id)) (tallyRegCost_comp_poly inOPoly_id))
    (monoUB_double_poly ct kt dt)

theorem initBound_poly (W q : Nat) : inOPoly (fun n => initBound W q n n) := by
  unfold initBound bitBound
  have BB : inOPoly (fun n => n + 3 + n * (n + 2 * W + 10) + n * n) :=
    inOPoly_add (inOPoly_add (inOPoly_add inOPoly_id (inOPoly_const 3))
      (inOPoly_mul inOPoly_id (inOPoly_add (inOPoly_add inOPoly_id (inOPoly_const _))
        (inOPoly_const 10)))) (inOPoly_mul inOPoly_id inOPoly_id)
  exact inOPoly_add (inOPoly_add (inOPoly_add (inOPoly_add (inOPoly_const 60)
    (inOPoly_const _)) (inOPoly_const _)) BB) BB

theorem loopBound_poly (M : FlatTM) (ct kt dt : Nat) :
    inOPoly (fun n => loopBound M (budget ct kt dt n) n) := by
  unfold loopBound
  have BT := budget_poly ct kt dt
  exact inOPoly_add (inOPoly_add (inOPoly_const 1) (inOPoly_mul BT (inOPoly_mul (inOPoly_const _)
    (inOPoly_add (inOPoly_add (inOPoly_add (inOPoly_mul (inOPoly_const _)
      (inOPoly_add (inOPoly_add inOPoly_id (inOPoly_const 4)) BT)) BT) (inOPoly_const _))
      (inOPoly_const 2))))) (inOPoly_mul BT BT)

theorem simBound_poly (M : FlatTM) (acc a k b ct kt dt : Nat) :
    inOPoly (simBound M acc a k b ct kt dt) := by
  show inOPoly (fun n => 4 + lenBound a k b n n + timerBound ct kt dt n n
    + initBound (wid M) M.start n n + loopBound M (budget ct kt dt n) n
    + (3 * acc + M.states + 10))
  exact inOPoly_add (inOPoly_add (inOPoly_add (inOPoly_add (inOPoly_add (inOPoly_const 4)
    (lenBound_poly a k b)) (timerBound_poly ct kt dt)) (initBound_poly _ _))
    (loopBound_poly M ct kt dt)) (inOPoly_const _)

theorem simBound_mono (M : FlatTM) (acc a k b ct kt dt : Nat) :
    monotonic (simBound M acc a k b ct kt dt) := by
  intro x y hxy
  have h1 := lenBound_mono a k b hxy hxy
  have h2 := timerBound_mono ct kt dt hxy hxy
  have h3 := initBound_mono (wid M) M.start hxy hxy
  have hb : budget ct kt dt x ≤ budget ct kt dt y := by unfold budget; gcongr
  have h4 : loopBound M (budget ct kt dt x) x ≤ loopBound M (budget ct kt dt y) y := by
    unfold loopBound; gcongr
  have h5 : lenBound a k b x x ≤ lenBound a k b y y := by
    have := lenBound_mono a k b (le_refl x) (le_refl x)
    exact lenBound_mono a k b hxy hxy
  have h6 : timerBound ct kt dt x x ≤ timerBound ct kt dt y y := timerBound_mono ct kt dt hxy hxy
  have h7 : initBound (wid M) M.start x x ≤ initBound (wid M) M.start y y :=
    initBound_mono (wid M) M.start hxy hxy
  unfold simBound
  omega

/-! ## The witness -/

theorem stepCfg_iterate_eq (M : FlatTM) (cfg cfg' : FlatTMConfig) (t T : Nat) (hT : t ≤ T)
    (hrun : runFlatTM t M cfg = some cfg') (hh : haltingStateReached M cfg' = true) :
    (stepCfg M)^[T] cfg = cfg' := by
  have := runFlatTM_extend (k := T - t) hrun hh
  rw [show t + (T - t) = T by omega, runFlatTM_eq_iterate] at this
  exact Option.some.inj this

theorem size_pair_ge (x c : List Bool) : x.length + c.length ≤ encodable.size (x, c) := by
  have h1 := length_le_size x
  have h2 := length_le_size c
  show x.length + c.length ≤ encodable.size x + encodable.size c + 1
  omega

theorem certState_pair (x c : List Bool) : certState x ++ certState c = inputState x c := rfl

/-- **Every language in NP has a polynomial-cost verifier program.** -/
theorem inNP_inNPCmd {Q : List Bool → Prop} (h : inNP Q) : inNPCmd Q := by
  classical
  obtain ⟨R, a, k, b, t, M, acc, rej, ht, hM, h1, hQ, hdec⟩ := h
  obtain ⟨ct, kt, dt, htb⟩ := inOPoly_monomial_bound ht
  let rel : List Bool → List Bool → Prop := fun x c => c.length ≤ a * x.length ^ k + b ∧ R x c
  let dB : Nat → Nat := fun n => n + simBound M acc a k b ct kt dt n
  have dB_poly : inOPoly dB := inOPoly_add inOPoly_id (simBound_poly M acc a k b ct kt dt)
  have dB_mono : monotonic dB := fun u v huv =>
    Nat.add_le_add huv (simBound_mono M acc a k b ct kt dt u v huv)
  have dB_ge : ∀ n, n ≤ dB n := fun n => Nat.le_add_right n _
  -- the verdict of the program
  have hverdict : ∀ x c : List Bool,
      State.get ((simTM M acc a k b ct kt dt).eval (inputState x c)) 0
        = if rel x c then [1] else [0] := by
    intro x c
    obtain ⟨cfg, hrun, hh, hacc, -⟩ := hdec x c
    have hit := stepCfg_iterate_eq M _ cfg (t (x.length + c.length))
      (budget ct kt dt (x.length + c.length)) (htb _) hrun hh
    have hg := simTM_get M hM h1 acc a k b ct kt dt x c
    rw [hit] at hg
    show State.get _ XO = _
    rw [hg]
    by_cases hr : rel x c
    · rw [if_pos hr, if_pos ⟨hacc.mp hr.2, hr.1⟩]
    · rw [if_neg hr, if_neg (fun h => hr ⟨h.2, hacc.mpr h.1⟩)]
  let V : DecidesLang (fun xc : List Bool × List Bool => rel xc.1 xc.2) dB :=
    { c := simTM M acc a k b ct kt dt
      encodeIn := fun xc => certState xc.1 ++ certState xc.2
      encodeIn_size := fun xc => by
        obtain ⟨x, c⟩ := xc
        refine le_trans ?_ (le_trans (size_pair_ge x c) (dB_ge _))
        show State.size [bitsOf x, bitsOf c] ≤ _
        simp [State.size, bitsOf]
      decides := fun xc => by
        obtain ⟨x, c⟩ := xc
        show (rel x c ↔ (State.get ((simTM M acc a k b ct kt dt).eval (inputState x c)) 0
            == [1]) = true) ∧ (¬ rel x c ↔ (State.get ((simTM M acc a k b ct kt dt).eval
            (inputState x c)) 0 == [0]) = true)
        rw [hverdict x c]
        by_cases hr : rel x c <;> simp [hr]
      cost_bound := fun xc => by
        obtain ⟨x, c⟩ := xc
        show (simTM M acc a k b ct kt dt).cost (inputState x c) ≤ _
        refine le_trans (simTM_cost M hM h1 acc a k b ct kt dt x c) ?_
        refine le_trans ?_ (dB_mono _ _ (size_pair_ge x c))
        exact Nat.le_add_left _ _
      enc_bit := fun xc => by
        obtain ⟨x, c⟩ := xc
        intro reg hreg v hv
        simp only [certState, List.cons_append, List.nil_append, List.mem_cons,
          List.mem_nil_iff, or_false] at hreg
        rcases hreg with rfl | rfl <;>
          (simp only [List.mem_map] at hv; obtain ⟨bb, _, rfl⟩ := hv; split <;> omega)
      regBound := REGS
      usesBelow := simTM_ub M acc a k b ct kt dt
      width_le := fun _ => by simp [certState, REGS] }
  have hcert : polyCertRel Q rel := ⟨{
    bound := fun m => 2 * (a * m ^ k + b)
    sound := fun x c hr => (hQ x).mpr ⟨c, hr.1, hr.2⟩
    complete := fun x hx => by
      obtain ⟨c, hc, hR⟩ := (hQ x).mp hx
      refine ⟨c, ⟨hc, hR⟩, ?_⟩
      have h1 := size_le_two_mul_length c
      have h2 : a * x.length ^ k ≤ a * (encodable.size x) ^ k :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (length_le_size x) k)
      show encodable.size c ≤ 2 * (a * (encodable.size x) ^ k + b)
      omega
    bound_poly := inOPoly_mul (inOPoly_const 2)
      (inOPoly_add (inOPoly_mul (inOPoly_const a) (inOPoly_pow' k)) (inOPoly_const b))
    bound_mono := fun u v huv => by
      show 2 * (a * u ^ k + b) ≤ 2 * (a * v ^ k + b)
      gcongr }⟩
  exact ⟨{
    rel := rel
    dBound := dB
    dBound_poly := dB_poly
    dBound_mono := dB_mono
    verifier := V
    rel_correct := hcert
    encX := certState
    encodeIn_eq := fun _ _ => rfl
    xWidth := 1
    encX_width := fun _ => rfl
    encX_size := fun x => by
      rw [State.size_certState]
      exact le_trans (length_le_size x) (dB_ge _)
    sizeLB := fun n => 2 * n
    sizeLB_poly := inOPoly_mul (inOPoly_const 2) inOPoly_id
    encX_sizeLB := fun x => by
      rw [State.size_certState]; exact size_le_two_mul_length x
    encX_canonical := fun _ => rfl }⟩

end CookLevin.Sim
