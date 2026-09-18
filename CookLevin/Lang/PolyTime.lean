import CookLevin.Lang.Compile
import CookLevin.Lang.Frame
import CookLevin.Basic.NP

set_option autoImplicit false

/-! # Polynomial-cost programs

The reductions and verifiers of this development are programs of the register language
(`Lang/Syntax.lean`, `Lang/Semantics.lean`). This file defines what it means for such a
program to decide a predicate (`DecidesLang`) or to compute a function
(`PolyTimeComputableLang`) within a polynomial cost bound, how two computing programs are
composed (`SeamData`, `comp`), how a decider is precomposed with a program
(`precomposeFree`), and what it means to present a language by a verifier program
(`NPWitness`).

Input sizes are measured by `encodable.size` and running cost by `Cmd.cost`; `inOPoly` and
`monotonic` are defined in `Basic/Definitions.lean`. Every program is required to keep its
registers bit-shaped (`Compile.BitState`: every cell is `0` or `1`), which is what the
compiler to Turing machines (`Lang/Compile.lean`) needs. -/

namespace CookLevin.Lang

/-- `inOPoly` is closed under pointwise domination. -/
theorem inOPoly_of_le {f g : Nat → Nat} (hle : ∀ n, f n ≤ g n) (hg : inOPoly g) :
    inOPoly f := by
  obtain ⟨d, c, n0, h⟩ := hg
  exact ⟨d, c, n0, fun n hn => Nat.le_trans (hle n) (h n hn)⟩

/-- A program `c` decides `P` within cost `costBound`: run on the state `encodeIn x` it
accepts exactly when `P x` holds and rejects exactly when it does not, at a cost of at most
`costBound (encodable.size x)`. The remaining fields bound the input layout (its size, its
bit-shapedness, its width in registers) and the registers the program touches. -/
structure DecidesLang {X : Type} [encodable X]
    (P : X → Prop) (costBound : Nat → Nat) where
  /-- The program. -/
  c : Cmd
  /-- The layout of the input in the program's initial state. -/
  encodeIn : X → State
  /-- The input layout has size at most `costBound`. -/
  encodeIn_size : ∀ x, State.size (encodeIn x) ≤ costBound (encodable.size x)
  /-- The program accepts exactly the positive instances and rejects the others. -/
  decides : Cmd.decides c encodeIn P
  /-- The running cost is at most `costBound (encodable.size x)`. -/
  cost_bound : ∀ x, c.cost (encodeIn x) ≤ costBound (encodable.size x)
  /-- Every cell of the input layout is `0` or `1`. -/
  enc_bit : ∀ x, Compile.BitState (encodeIn x)
  /-- The program touches only registers below `regBound`. -/
  regBound : Nat
  usesBelow : Cmd.UsesBelow c regBound
  /-- The input layout uses at most `regBound` registers. -/
  width_le : ∀ x, (encodeIn x).length ≤ regBound

/-- A program `c` computes `f` within cost `cost_bound`: run on the state `encodeIn x`, its
final state decodes (through `decodeOut`) to `f x`, at a cost of at most
`cost_bound (encodable.size x)`; `output_size_le` bounds the size of `f x`, and
`decode_agree` says that `decodeOut` ignores registers the program never uses. The remaining
fields are as in `DecidesLang`. -/
structure PolyTimeComputableLang {X Y : Type} [encodable X] [encodable Y]
    (f : X → Y) where
  /-- The program. -/
  c : Cmd
  /-- The layout of the input in the program's initial state. -/
  encodeIn : X → State
  /-- How the output is read off the final state. -/
  decodeOut : State → Y
  /-- The cost bound, a monotone polynomial. -/
  cost_bound : Nat → Nat
  cost_bound_poly : inOPoly cost_bound
  cost_bound_mono : monotonic cost_bound
  /-- A monotone polynomial bounding the size of the input layout. -/
  encBound : Nat → Nat
  encBound_poly : inOPoly encBound
  encBound_mono : monotonic encBound
  encodeIn_size : ∀ x, State.size (encodeIn x) ≤ encBound (encodable.size x)
  /-- After running `c`, the final state decodes to `f x`. -/
  computes : ∀ x, decodeOut (c.eval (encodeIn x)) = f x
  /-- The running cost is at most `cost_bound (encodable.size x)`. -/
  cost_le : ∀ x, c.cost (encodeIn x) ≤ cost_bound (encodable.size x)
  /-- The output size is at most `cost_bound (encodable.size x)`. -/
  output_size_le : ∀ x, encodable.size (f x) ≤ cost_bound (encodable.size x)
  /-- Every cell of the input layout is `0` or `1`. -/
  enc_bit : ∀ x, Compile.BitState (encodeIn x)
  /-- The program touches only registers below `regBound`. -/
  regBound : Nat
  usesBelow : Cmd.UsesBelow c regBound
  /-- The input layout uses at most `regBound` registers. -/
  width_le : ∀ x, (encodeIn x).length ≤ regBound
  /-- Padding the input with empty registers does not change the decoded output. -/
  decode_agree : ∀ x (m : Nat),
    decodeOut (c.eval (encodeIn x ++ List.replicate m []))
      = decodeOut (c.eval (encodeIn x))

/-! ## Composing two computing programs

Two programs `Wf` (computing `f`) and `Wg` (computing `g`) are composed by running `Wf`, then
a re-encoding program `mfc` that moves `Wf`'s output into `Wg`'s input layout, then `Wg`. The
data needed for one such seam is `SeamData`; `comp` builds the composite program and proves
all its bounds from the seam data. -/

/-- The data of a seam between `Wf` and `Wg`. -/
structure PolyTimeComputableLang.SeamData
    {X Y Z : Type} [encodable X] [encodable Y] [encodable Z]
    {f : X → Y} {g : Y → Z}
    (Wf : PolyTimeComputableLang f) (Wg : PolyTimeComputableLang g) where
  /-- The re-encoding program. -/
  mfc : Cmd
  /-- After `Wf.c ;; mfc`, the state agrees with `Wg`'s own input layout of `f x` on all
  registers `Wg` uses. -/
  bridge : ∀ x, AgreeBelow Wg.regBound
    (mfc.eval (Wf.c.eval (Wf.encodeIn x))) (Wg.encodeIn (f x))
  /-- `Wg.decodeOut` depends only on the registers `Wg` uses. -/
  decode_frame : ∀ s t, AgreeBelow Wg.regBound s t →
    Wg.decodeOut s = Wg.decodeOut t
  /-- The re-encoder's cost bound, a monotone polynomial. -/
  mfcBound : Nat → Nat
  mfcBound_poly : inOPoly mfcBound
  mfcBound_mono : monotonic mfcBound
  mfc_cost : ∀ x, mfc.cost (Wf.c.eval (Wf.encodeIn x))
    ≤ mfcBound (encodable.size x)
  /-- The re-encoder stays inside the composite's registers. -/
  mfc_usesBelow : Cmd.UsesBelow mfc (max Wf.regBound Wg.regBound)

/-- Padding a state with empty registers changes no register read. -/
theorem State.get_append_replicate_nil (s : State) (m : Nat) (r : Var) :
    State.get (s ++ List.replicate m []) r = State.get s r := by
  unfold State.get
  rcases Nat.lt_or_ge r s.length with h | h
  · rw [List.getElem?_append_left h]
  · rw [List.getElem?_eq_none h]
    rcases Nat.lt_or_ge r (s ++ List.replicate m ([] : List Nat)).length with h2 | h2
    · rw [List.getElem?_eq_getElem h2]
      have hnil : (s ++ List.replicate m ([] : List Nat))[r]'h2 = [] := by
        rw [List.getElem_append_right h]
        exact List.getElem_replicate _
      rw [hnil]
      rfl
    · rw [List.getElem?_eq_none h2]

/-- The composite of two computing programs across a seam. -/
def PolyTimeComputableLang.comp
    {X Y Z : Type} [encodable X] [encodable Y] [encodable Z]
    {f : X → Y} {g : Y → Z}
    (Wf : PolyTimeComputableLang f) (Wg : PolyTimeComputableLang g)
    (S : Wf.SeamData Wg) : PolyTimeComputableLang (g ∘ f) where
  c := Wf.c ;; (S.mfc ;; Wg.c)
  encodeIn := Wf.encodeIn
  decodeOut := Wg.decodeOut
  cost_bound := fun n =>
    Wf.cost_bound n + S.mfcBound n + Wg.cost_bound (Wf.cost_bound n) + 2
  cost_bound_poly :=
    inOPoly_add (inOPoly_add (inOPoly_add Wf.cost_bound_poly S.mfcBound_poly)
      (inOPoly_comp Wf.cost_bound_poly Wg.cost_bound_poly)) (inOPoly_const 2)
  cost_bound_mono := fun a b h => by
    have h1 := Wf.cost_bound_mono a b h
    have h2 := S.mfcBound_mono a b h
    have h3 := Wg.cost_bound_mono _ _ h1
    show Wf.cost_bound a + S.mfcBound a + Wg.cost_bound (Wf.cost_bound a) + 2
        ≤ Wf.cost_bound b + S.mfcBound b + Wg.cost_bound (Wf.cost_bound b) + 2
    omega
  encBound := Wf.encBound
  encBound_poly := Wf.encBound_poly
  encBound_mono := Wf.encBound_mono
  encodeIn_size := Wf.encodeIn_size
  computes := fun x => by
    show Wg.decodeOut ((Wf.c ;; (S.mfc ;; Wg.c)).eval (Wf.encodeIn x)) = g (f x)
    rw [Cmd.eval_seq, Cmd.eval_seq]
    have hagree := Cmd.eval_agree Wg.c Wg.regBound Wg.usesBelow (S.bridge x)
    rw [S.decode_frame _ _ hagree]
    exact Wg.computes (f x)
  cost_le := fun x => by
    have h1 := Wf.cost_le x
    have h2 := S.mfc_cost x
    have hgc : Wg.c.cost (S.mfc.eval (Wf.c.eval (Wf.encodeIn x)))
        = Wg.c.cost (Wg.encodeIn (f x)) :=
      Cmd.cost_agree Wg.c Wg.regBound Wg.usesBelow (S.bridge x)
    have h3 := Wg.cost_le (f x)
    have h4 := Wg.cost_bound_mono _ _ (Wf.output_size_le x)
    show (Wf.c ;; (S.mfc ;; Wg.c)).cost (Wf.encodeIn x) ≤ _
    rw [Cmd.cost_seq, Cmd.cost_seq]
    omega
  output_size_le := fun x => by
    show encodable.size (g (f x)) ≤ _
    have h1 := Wg.output_size_le (f x)
    have h2 := Wg.cost_bound_mono _ _ (Wf.output_size_le x)
    omega
  enc_bit := Wf.enc_bit
  regBound := max Wf.regBound Wg.regBound
  usesBelow :=
    ⟨Cmd.UsesBelow_mono (Nat.le_max_left _ _) Wf.usesBelow,
     S.mfc_usesBelow,
     Cmd.UsesBelow_mono (Nat.le_max_right _ _) Wg.usesBelow⟩
  width_le := fun x =>
    le_trans (Wf.width_le x) (Nat.le_max_left _ _)
  decode_agree := fun x m => by
    have hpad : AgreeBelow (max Wf.regBound Wg.regBound)
        (Wf.encodeIn x ++ List.replicate m []) (Wf.encodeIn x) :=
      fun r _ => State.get_append_replicate_nil (Wf.encodeIn x) m r
    show Wg.decodeOut ((Wf.c ;; (S.mfc ;; Wg.c)).eval
        (Wf.encodeIn x ++ List.replicate m []))
      = Wg.decodeOut ((Wf.c ;; (S.mfc ;; Wg.c)).eval (Wf.encodeIn x))
    rw [Cmd.eval_seq, Cmd.eval_seq, Cmd.eval_seq, Cmd.eval_seq]
    have h1 := Cmd.eval_agree Wf.c _
      (Cmd.UsesBelow_mono (Nat.le_max_left _ _) Wf.usesBelow) hpad
    have h2 := Cmd.eval_agree S.mfc _ S.mfc_usesBelow h1
    have h3 := Cmd.eval_agree Wg.c _
      (Cmd.UsesBelow_mono (Nat.le_max_right _ _) Wg.usesBelow) h2
    exact S.decode_frame _ _
      (fun r hr => h3 r (Nat.lt_of_lt_of_le hr (Nat.le_max_right _ _)))

/-! ## Precomposing a decider with a program

A decider `D` for `Q` is turned into a decider for `fun v => Q (gmap v)` by running a
re-encoding program `mfc` first: `mfc` computes `gmap v` from the layout `eIn v` and leaves
it in `D`'s input layout. -/

/-- The data needed to precompose `D` with `gmap`. -/
structure DecidesLang.FreePrecomposeData {V W : Type} [encodable V] [encodable W]
    {Q : W → Prop} {dBound : Nat → Nat} (D : DecidesLang Q dBound) (gmap : V → W) where
  /-- The re-encoding program. -/
  mfc : Cmd
  /-- The composite's input layout. -/
  eIn : V → State
  /-- The composite's cost bound, a monotone polynomial. -/
  newBound : Nat → Nat
  newBound_poly : inOPoly newBound
  newBound_mono : monotonic newBound
  /-- After `mfc`, the state agrees with `D`'s own input layout of `gmap v` on all registers
  `D` uses. -/
  bridge : ∀ v, AgreeBelow D.regBound (mfc.eval (eIn v)) (D.encodeIn (gmap v))
  encodeIn_size : ∀ v, State.size (eIn v) ≤ newBound (encodable.size v)
  cost_bound : ∀ v, (mfc ;; D.c).cost (eIn v) ≤ newBound (encodable.size v)
  enc_bit : ∀ v, Compile.BitState (eIn v)
  regBound : Nat
  usesBelow : Cmd.UsesBelow (mfc ;; D.c) regBound
  width_le : ∀ v, (eIn v).length ≤ regBound

/-- The decider for `fun v => Q (gmap v)` obtained by precomposition. -/
def DecidesLang.precomposeFree {V W : Type} [encodable V] [encodable W]
    {Q : W → Prop} {dBound : Nat → Nat} (D : DecidesLang Q dBound) (gmap : V → W)
    (data : D.FreePrecomposeData gmap) :
    DecidesLang (fun v => Q (gmap v)) data.newBound where
  c := data.mfc ;; D.c
  encodeIn := data.eIn
  encodeIn_size := data.encodeIn_size
  decides := fun v => by
    have hagree : AgreeBelow D.regBound (D.c.eval (data.mfc.eval (data.eIn v)))
        (D.c.eval (D.encodeIn (gmap v))) :=
      Cmd.eval_agree D.c D.regBound D.usesBelow (data.bridge v)
    have h0 : State.get ((data.mfc ;; D.c).eval (data.eIn v)) 0
        = State.get (D.c.eval (D.encodeIn (gmap v))) 0 := by
      rw [Cmd.eval_seq]
      exact hagree 0 (Cmd.UsesBelow_pos D.usesBelow)
    have hacc : ((data.mfc ;; D.c).eval (data.eIn v)).isAccept
        = (D.c.eval (D.encodeIn (gmap v))).isAccept := by
      show (State.get ((data.mfc ;; D.c).eval (data.eIn v)) 0 == [1])
          = (State.get (D.c.eval (D.encodeIn (gmap v))) 0 == [1])
      rw [h0]
    have hrej : ((data.mfc ;; D.c).eval (data.eIn v)).isReject
        = (D.c.eval (D.encodeIn (gmap v))).isReject := by
      show (State.get ((data.mfc ;; D.c).eval (data.eIn v)) 0 == [0])
          = (State.get (D.c.eval (D.encodeIn (gmap v))) 0 == [0])
      rw [h0]
    refine ⟨?_, ?_⟩
    · rw [hacc]; exact (D.decides (gmap v)).1
    · rw [hrej]; exact (D.decides (gmap v)).2
  cost_bound := data.cost_bound
  enc_bit := data.enc_bit
  regBound := data.regBound
  usesBelow := data.usesBelow
  width_le := data.width_le

/-! ## NP witnesses

A language `P` is presented by a verifier program: a decider for a certificate relation
`rel` on pairs `(x, c)`, where the certificate `c` is a bit string and the pair is laid out
as the input layout `encX x` followed by the certificate in the canonical one-register
layout `certState c`. -/

/-- The canonical layout of a bit string: one register holding one cell per bit,
`false ↦ 0`, `true ↦ 1`. -/
def certState (c : List Bool) : State := [c.map (fun b => if b then 1 else 0)]

/-- A verifier program for `P`, with its input layout `encX`. -/
structure NPWitness {X : Type} [encodable X] (P : X → Prop) where
  /-- The certificate relation. -/
  rel : X → List Bool → Prop
  /-- The verifier's cost bound, a monotone polynomial. -/
  dBound : Nat → Nat
  dBound_poly : inOPoly dBound
  dBound_mono : monotonic dBound
  /-- The verifier: a program deciding `rel` on pairs `(x, c)`. -/
  verifier : DecidesLang (fun xc : X × List Bool => rel xc.1 xc.2) dBound
  /-- `rel` is a sound and complete certificate relation for `P`, with certificates of
  polynomially bounded size. -/
  rel_correct : polyCertRel P rel
  /-- The layout of the input `x`. -/
  encX : X → State
  /-- The verifier reads the pair as the input layout followed by the certificate register. -/
  encodeIn_eq : ∀ x c, verifier.encodeIn (x, c) = encX x ++ certState c
  /-- The input layout has a fixed number of registers. -/
  xWidth : Nat
  encX_width : ∀ x, (encX x).length = xWidth
  /-- The input layout has size at most `dBound`. -/
  encX_size : ∀ x, State.size (encX x) ≤ dBound (encodable.size x)
  /-- The input layout does not compress: the size of `x` is bounded by a polynomial in the
  number of cells of its layout. -/
  sizeLB : Nat → Nat
  sizeLB_poly : inOPoly sizeLB
  encX_sizeLB : ∀ x, encodable.size x ≤ sizeLB (State.size (encX x))

end CookLevin.Lang
