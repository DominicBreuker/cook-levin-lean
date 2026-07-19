import Complexity.Simulators.CookTableau

set_option autoImplicit false

/-! # The prelude/cert-guess layer (Risk S1, step 2) — design + skeleton

`CookTableau.lean` is the **deterministic core**: `cookTableau_correct`
(sorry-free & axiom-clean, 2026-07-18-d) says `acceptsFlatTM M [s] steps ↔`
the tableau covers. The S1 *reduction* target `FlatSingleTMGenNP` instead
asks `∃ cert, … ∧ acceptsFlatTM M [s ++ cert] steps` — the certificate must
become **tableau nondeterminism**. This file adds the Coq port's
`preludeRules` idea (see `coqdoc/…PTCC_Preludes.txt` and
`…SingleTMGenNP_to_TCC.txt`): row 0 becomes a *prelude* row containing
wildcard cells over the cert region; the cards resolving them fire exactly
once (row 0 → row 1) and produce the deterministic core's initial row for
`s ++ cert`, for a nondeterministically guessed `cert`; the budget grows to
`steps + 1`.

## Design decisions (risk review 2026-07-19 — read before extending)

1. **Band-disjoint prelude alphabet; the proven core is reused UNCHANGED.**
   The HANDOFF risk was that wildcard cells are a fourth code band that
   might re-open the (1a)/(1b) card-family audits. Resolution: the prelude
   symbols live in a fresh band `[Sg M, PSg M)` **above** the Γ band
   (`PSg M = Sg M + 2·M.sig + 5`); prelude card *premises* are entirely
   prelude-band and their *conclusions* entirely Γ-band (Coq's
   `liftPrelude`/`liftOrig` sum-type discipline, done here with flat code
   bands). Consequences, purely by band mismatch:
   * prelude cards can never fire on a Γ row (their premises match no
     Γ window), so rows 1…steps+1 step exactly by the embedded `cookCards`
     — `validStep_emb`/`relpower_emb` transfer the four proven directions
     through the value-preserving embedding `emb : Fin (Sg M) → Fin (PSg M)`
     and **nothing in `CookTableau.lean` changes**;
   * Γ cards can never fire on the (all-prelude) row 0, so the prelude step
     is fully described by the prelude card table (`cert_of_prelude_validStep`
     is a self-contained inversion over a row of statically known shape);
   * a chain of length `steps + 1` from row 0 therefore consists of exactly
     one prelude step followed by `steps` Γ steps — the prelude is
     special-cased *outside* the trajectory induction, as planned.
2. **Everything known at construction time is baked into row 0's symbols**
   (`pSig σ` carries the fixed input symbol, `pInitSig σ`/`pInitStar`/
   `pInitBlank` mark the head position), so `preludeCards M` depends only on
   `M` — like `cookCards`, the card list is instance-shape-independent and
   the prelude rules need no access to `s`.
3. **The head cell.** Our rows carry the head as `hCell (state, symbol)`,
   so the row-1 cell at tape position 0 depends on the (possibly guessed)
   symbol there. Position 0 of row 0 gets an `Init`-variant prelude symbol
   (`pInitSig s[0]` when `s ≠ []`, `pInitStar` when position 0 is a cert
   cell, `pInitBlank` when it is beyond the cert region), whose resolutions
   are exactly the corresponding `hCell (stateOf M.start) ·` cells.
4. **Cert contiguity is window-local.** A guessed cert of length `c ≤
   maxSize` resolves the first `c` star cells to symbols `< M.sig` and the
   rest to blanks. `contigOK` forbids any card whose conclusion resolves a
   star to blank left of a star resolved to a symbol *within one window*;
   since adjacent cells share a window, the star region globally resolves
   as `symbols* blanks*` — the resolved row 1 IS `confRow` of
   `initFlatConfig M [s ++ cert]` (blanks at/beyond the frontier), with
   `cert` read off the live star cells. Symbols are `< M.sig` by card
   construction, giving `list_ofFlatType M.sig cert` for free in the
   inversion.
5. **Generic premise triples.** `preludeCards` enumerates ALL kind-triples,
   not just those occurring in some prelude row. Sound: a card fires on a
   window only when its premise *equals* the window, so never-occurring
   premises are dead weight; this keeps the definition uniform (three
   nested `flatMap`s) at `Θ(M.sig³)` cards — the same order as `copyCards`,
   so the eventual size bound stays degree-10.
6. **Width.** The interior needs room for `s`, the cert region, and the
   run: `guessWidth = |s| + maxSize + steps + 3`. The deterministic core's
   trajectory lemmas (`relpower_of_run`/`run_of_relpower`) are already
   `n`-generic; they are consumed at `n = guessWidth` with
   `base = |s ++ cert| ≤ |s| + maxSize` — no re-proving.

## Status (2026-07-19)

* All definitions landed and `#eval`-probed (`probes/S1TableauProbe.lean`
  §6: every cert resolution licensed; non-contiguous / out-of-region /
  wrong-state resolutions refuted; row 0 does not freeze; Γ rows cannot
  step back; end-to-end yes/no chains behave; `s = []` / `maxSize = 0`
  edge shapes covered).
* `guessTableau_correct` — **stated and ASSEMBLED (proven)** from four
  sorried sub-obligations, validating their statement shapes against the
  deterministic core's proven machinery:
  - `prelude_validStep_of_cert` (P1, the guess step forward);
  - `cert_of_prelude_validStep` (P2, the prelude inversion);
  - `validStep_emb` (T1, the Γ-step band transfer);
  - `relpower_emb` (T2, the Γ-chain transfer; `relpower_emb_of` is the
    proven forward companion).
  `satFinal_emb` (T3) and the band/shape lemmas are PROVEN.
* The eventual S1 free witness emits `guessTableau M s maxSize steps` from
  a `FlatSingleTMGenNP` instance `(M, s, maxSize, steps)`, guarded on
  exactly `guessTableau_correct`'s hypotheses (`validFlatTM` / `tapes = 1`
  / `list_ofFlatType` — all decidable; the guarded-map pattern). It will
  need a `guessTableau_size_bound` analogous to `cookTableau_size_bound`
  (the prelude adds `Θ(M.sig³)` cards — within the degree-10 budget). -/

namespace Complexity.Simulators

open FlatTCC TCC

/-! ## The extended alphabet: Γ band `[0, Sg M)` + prelude band `[Sg M, PSg M)`

Prelude band layout: `pDelim`, `pBlank`, `pStar`, `pInitStar`, `pInitBlank`
at `Sg M + 0 … + 4`, then `pSig σ` at `Sg M + 5 + σ` and `pInitSig σ` at
`Sg M + 5 + M.sig + σ` for `σ < M.sig`. -/

/-- The guess-tableau alphabet size. -/
def PSg (M : FlatTM) : Nat := Sg M + (2 * M.sig + 5)

/-- The value-preserving embedding of the deterministic core's alphabet. -/
def emb (M : FlatTM) (c : Fin (Sg M)) : Fin (PSg M) :=
  ⟨c.1, by have := c.2; unfold PSg; omega⟩

theorem emb_inj (M : FlatTM) {a b : Fin (Sg M)} (h : emb M a = emb M b) :
    a = b := by
  have hv : (emb M a).1 = (emb M b).1 := congrArg Fin.val h
  exact Fin.ext hv

theorem emb_val_lt (M : FlatTM) (c : Fin (Sg M)) : (emb M c).1 < Sg M := c.2

/-- Card embedding (premise and conclusion cell-wise). -/
def embCard (M : FlatTM) (c : TCCCard (Fin (Sg M))) : TCCCard (Fin (PSg M)) :=
  { prem := ⟨emb M c.prem.cardEl1, emb M c.prem.cardEl2, emb M c.prem.cardEl3⟩,
    conc := ⟨emb M c.conc.cardEl1, emb M c.conc.cardEl2, emb M c.conc.cardEl3⟩ }

/-- Prelude symbol: the row delimiter (resolves to the boundary marker). -/
def pDelim (M : FlatTM) : Fin (PSg M) := ⟨Sg M, by unfold PSg; omega⟩

/-- Prelude symbol: a definitely-blank position (beyond the cert region). -/
def pBlank (M : FlatTM) : Fin (PSg M) := ⟨Sg M + 1, by unfold PSg; omega⟩

/-- Prelude symbol: a cert wildcard. -/
def pStar (M : FlatTM) : Fin (PSg M) := ⟨Sg M + 2, by unfold PSg; omega⟩

/-- Prelude symbol: the head position over a cert wildcard (`s = []`). -/
def pInitStar (M : FlatTM) : Fin (PSg M) := ⟨Sg M + 3, by unfold PSg; omega⟩

/-- Prelude symbol: the head position over a definitely-blank cell
(`s = []` and `maxSize = 0`). -/
def pInitBlank (M : FlatTM) : Fin (PSg M) := ⟨Sg M + 4, by unfold PSg; omega⟩

/-- Prelude symbol: a fixed input symbol (a cell of `s` after position 0). -/
def pSig (M : FlatTM) (σ : Fin M.sig) : Fin (PSg M) :=
  ⟨Sg M + 5 + σ.1, by have := σ.2; unfold PSg; omega⟩

/-- Prelude symbol: the head position over fixed input symbol `s[0]`. -/
def pInitSig (M : FlatTM) (σ : Fin M.sig) : Fin (PSg M) :=
  ⟨Sg M + 5 + M.sig + σ.1, by have := σ.2; unfold PSg; omega⟩

/-! ## Prelude cell kinds, resolutions, and the card table -/

/-- The kind of a prelude-row cell. -/
inductive PKind (M : FlatTM) where
  | delim
  | blank
  | star
  | initStar
  | initBlank
  | fixedSym (σ : Fin M.sig)
  | initFixedSym (σ : Fin M.sig)

/-- The prelude symbol of a kind. -/
def pCell (M : FlatTM) : PKind M → Fin (PSg M)
  | .delim => pDelim M
  | .blank => pBlank M
  | .star => pStar M
  | .initStar => pInitStar M
  | .initBlank => pInitBlank M
  | .fixedSym σ => pSig M σ
  | .initFixedSym σ => pInitSig M σ

/-- Resolution class of one cell, for the window-local contiguity filter:
deterministic cells are `other`; a star resolved to a cert symbol is
`live`; a star resolved to the blank (the cert has ended) is `cut`. -/
inductive PRes where
  | other
  | live
  | cut
deriving DecidableEq

/-- All resolutions of one prelude cell: the Γ cell it may become in row 1,
tagged with its resolution class. -/
def pResolutions (M : FlatTM) : PKind M → List (Fin (Sg M) × PRes)
  | .delim => [(bCell M, .other)]
  | .blank => [(tCell M (blankSym M), .other)]
  | .fixedSym σ => [(tCell M ⟨σ.1, Nat.lt_succ_of_lt σ.2⟩, .other)]
  | .initFixedSym σ =>
      [(hCell M (stateOf M M.start) ⟨σ.1, Nat.lt_succ_of_lt σ.2⟩, .other)]
  | .initBlank => [(hCell M (stateOf M M.start) (blankSym M), .other)]
  | .star =>
      (List.finRange M.sig).map
        (fun σ => (tCell M ⟨σ.1, Nat.lt_succ_of_lt σ.2⟩, PRes.live))
        ++ [(tCell M (blankSym M), .cut)]
  | .initStar =>
      (List.finRange M.sig).map
        (fun σ => (hCell M (stateOf M M.start) ⟨σ.1, Nat.lt_succ_of_lt σ.2⟩,
          PRes.live))
        ++ [(hCell M (stateOf M M.start) (blankSym M), .cut)]

/-- Window-local cert contiguity: no `cut` left of a `live`. Overlapping
windows make this global (design decision 4). -/
def contigOK : PRes → PRes → PRes → Bool
  | .cut, .live, _ => false
  | .cut, _, .live => false
  | _, .cut, .live => false
  | _, _, _ => true

/-- All prelude cell kinds (for card enumeration). -/
def pKindList (M : FlatTM) : List (PKind M) :=
  [.delim, .blank, .star, .initStar, .initBlank]
    ++ (List.finRange M.sig).map PKind.fixedSym
    ++ (List.finRange M.sig).map PKind.initFixedSym

/-- The prelude cards of one premise kind-triple: all contiguity-respecting
resolutions. Premises are prelude-band, conclusions Γ-band. -/
def preludeCardsOf (M : FlatTM) (k1 k2 k3 : PKind M) :
    List (TCCCard (Fin (PSg M))) :=
  (pResolutions M k1).flatMap (fun r1 =>
    (pResolutions M k2).flatMap (fun r2 =>
      (pResolutions M k3).filterMap (fun r3 =>
        if contigOK r1.2 r2.2 r3.2 then
          some { prem := ⟨pCell M k1, pCell M k2, pCell M k3⟩,
                 conc := ⟨emb M r1.1, emb M r2.1, emb M r3.1⟩ }
        else none)))

/-- The full prelude card table (`Θ(M.sig³)` cards). -/
def preludeCards (M : FlatTM) : List (TCCCard (Fin (PSg M))) :=
  (pKindList M).flatMap (fun k1 =>
    (pKindList M).flatMap (fun k2 =>
      (pKindList M).flatMap (fun k3 => preludeCardsOf M k1 k2 k3)))

/-- All cards of the guess tableau: the embedded deterministic cards plus
the prelude cards. -/
def guessCards (M : FlatTM) : List (TCCCard (Fin (PSg M))) :=
  (cookCards M).map (embCard M) ++ preludeCards M

/-! ## The prelude row -/

/-- Interior row width: room for `s`, the cert region, and the run
(cf. `rowWidth`; the trajectory machinery is consumed at `n = guessWidth`). -/
def guessWidth (s : List Nat) (maxSize steps : Nat) : Nat :=
  s.length + maxSize + steps + 3

/-- The prelude kind of tape position `p`: a fixed input symbol on
`[0, |s|)`, a cert wildcard on `[|s|, |s| + maxSize)`, definitely blank
beyond; position 0 is promoted to its `Init` variant (the head). The
out-of-alphabet fallback (`s.getD p 0 ≥ M.sig`) is unreachable under
`list_ofFlatType M.sig s`. -/
def pKindAt (M : FlatTM) (s : List Nat) (maxSize : Nat) (p : Nat) : PKind M :=
  if p < s.length then
    if h : s.getD p 0 < M.sig then
      (if p = 0 then .initFixedSym ⟨s.getD p 0, h⟩ else .fixedSym ⟨s.getD p 0, h⟩)
    else (if p = 0 then .initBlank else .blank)
  else if p < s.length + maxSize then
    (if p = 0 then .initStar else .star)
  else (if p = 0 then .initBlank else .blank)

/-- Row 0 of the guess tableau: delimiters around `guessWidth` prelude
cells. -/
def preludeRow (M : FlatTM) (s : List Nat) (maxSize steps : Nat) :
    List (Fin (PSg M)) :=
  pDelim M ::
    (List.range (guessWidth s maxSize steps)).map
      (fun p => pCell M (pKindAt M s maxSize p))
    ++ [pDelim M]

theorem preludeRow_length (M : FlatTM) (s : List Nat) (maxSize steps : Nat) :
    (preludeRow M s maxSize steps).length = guessWidth s maxSize steps + 2 := by
  simp [preludeRow]

/-! ## The construction -/

/-- The final patterns, embedded (still: a halting head cell anywhere). -/
def guessFinal (M : FlatTM) : List (List (Fin (PSg M))) :=
  (cookFinal M).map (List.map (emb M))

/-- The guess tableau as a typed `TCC` instance: prelude row, combined
cards, budget `steps + 1`. -/
def guessTableauTyped (M : FlatTM) (s : List Nat) (maxSize steps : Nat) : TCC where
  Sigma := PSg M
  init := preludeRow M s maxSize steps
  cards := guessCards M
  final := guessFinal M
  steps := steps + 1

/-- **The guess tableau as a `FlatTCC` instance** — the S1 reduction's
image of a `FlatSingleTMGenNP` instance `(M, s, maxSize, steps)`. A genuine
computable function; no `if` on the source predicate's truth. -/
def guessTableau (M : FlatTM) (s : List Nat) (maxSize steps : Nat) : FlatTCC :=
  FlatTCC.flattenTCC (guessTableauTyped M s maxSize steps)

/-! ## Well-formedness (PROVEN) -/

theorem guessTableauTyped_wellformed (M : FlatTM) (s : List Nat)
    (maxSize steps : Nat) : TCC.wellformed (guessTableauTyped M s maxSize steps) := by
  unfold TCC.wellformed guessTableauTyped
  rw [preludeRow_length]
  unfold guessWidth
  omega

theorem guessTableau_wellformed (M : FlatTM) (s : List Nat) (maxSize steps : Nat) :
    FlatTCC.FlatTCC_wellformed (guessTableau M s maxSize steps) ∧
    FlatTCC.isValidFlattening (guessTableau M s maxSize steps) :=
  ⟨FlatTCC.flattenTCC_wellformed (guessTableauTyped_wellformed M s maxSize steps),
    FlatTCC.isValidFlattening_flattenTCC _⟩

/-! ## Band and shape lemmas (PROVEN) -/

theorem pCell_ge (M : FlatTM) (k : PKind M) : Sg M ≤ (pCell M k).1 := by
  cases k <;>
    simp only [pCell, pDelim, pBlank, pStar, pInitStar, pInitBlank, pSig,
      pInitSig] <;> omega

/-- Every prelude card is a resolution card: prelude-band premise triple,
Γ-band (embedded) conclusion triple. The workhorse for both the band
disjointness arguments and the prelude inversion. -/
theorem preludeCard_shape (M : FlatTM) {c : TCCCard (Fin (PSg M))}
    (h : c ∈ preludeCards M) :
    ∃ k1 k2 k3, ∃ r1 ∈ pResolutions M k1, ∃ r2 ∈ pResolutions M k2,
      ∃ r3 ∈ pResolutions M k3,
        contigOK r1.2 r2.2 r3.2 = true ∧
        c = { prem := ⟨pCell M k1, pCell M k2, pCell M k3⟩,
              conc := ⟨emb M r1.1, emb M r2.1, emb M r3.1⟩ } := by
  unfold preludeCards at h
  obtain ⟨k1, -, h⟩ := List.mem_flatMap.1 h
  obtain ⟨k2, -, h⟩ := List.mem_flatMap.1 h
  obtain ⟨k3, -, h⟩ := List.mem_flatMap.1 h
  unfold preludeCardsOf at h
  obtain ⟨r1, hr1, h⟩ := List.mem_flatMap.1 h
  obtain ⟨r2, hr2, h⟩ := List.mem_flatMap.1 h
  obtain ⟨r3, hr3, heq⟩ := List.mem_filterMap.1 h
  refine ⟨k1, k2, k3, r1, hr1, r2, hr2, r3, hr3, ?_⟩
  by_cases hc : contigOK r1.2 r2.2 r3.2 = true
  · rw [if_pos hc] at heq
    exact ⟨hc, (Option.some.inj heq).symm⟩
  · rw [if_neg hc] at heq
    cases heq

/-- Prelude card premises start in the prelude band — they can never match
a window of a Γ (embedded) row. -/
theorem preludeCard_prem_ge (M : FlatTM) {c : TCCCard (Fin (PSg M))}
    (h : c ∈ preludeCards M) : Sg M ≤ c.prem.cardEl1.1 := by
  obtain ⟨k1, k2, k3, r1, hr1, r2, hr2, r3, hr3, hcontig, hc⟩ :=
    preludeCard_shape M h
  rw [hc]
  exact pCell_ge M k1

/-- Embedded card premises are Γ-band — they can never match a window of
the (all-prelude) row 0. -/
theorem embCard_prem_lt (M : FlatTM) (c : TCCCard (Fin (Sg M))) :
    (embCard M c).prem.cardEl1.1 < Sg M := (c.prem.cardEl1).2

/-! ## The satFinal transfer (T3, PROVEN) -/

theorem isSubstring_singleton {α : Type} {x : α} {s : List α} :
    isSubstring [x] s ↔ x ∈ s := by
  constructor
  · rintro ⟨l, r, rfl⟩
    simp
  · intro hx
    obtain ⟨l, r, rfl⟩ := List.append_of_mem hx
    exact ⟨l, r, by simp⟩

/-- Every final pattern is a singleton halting head cell. -/
theorem cookFinal_shape (M : FlatTM) {pat : List (Fin (Sg M))}
    (h : pat ∈ cookFinal M) :
    ∃ q b, M.halt.getD q.1 false = true ∧ pat = [hCell M q b] := by
  unfold cookFinal at h
  obtain ⟨q, -, hq⟩ := List.mem_flatMap.1 h
  cases hh : M.halt.getD q.1 false with
  | false => rw [hh] at hq; simp at hq
  | true =>
    rw [hh] at hq
    simp only [if_true] at hq
    obtain ⟨b, -, rfl⟩ := List.mem_map.1 hq
    exact ⟨q, b, hh, rfl⟩

/-- The final condition transfers through the embedding (both ways). -/
theorem satFinal_emb (M : FlatTM) (b : List (Fin (Sg M))) :
    TCC.satFinal (guessFinal M) (b.map (emb M)) ↔
      TCC.satFinal (cookFinal M) b := by
  constructor
  · rintro ⟨subs, hmem, hsub⟩
    unfold guessFinal at hmem
    obtain ⟨pat, hpat, rfl⟩ := List.mem_map.1 hmem
    obtain ⟨q, cc, -, rfl⟩ := cookFinal_shape M hpat
    simp only [List.map_cons, List.map_nil] at hsub
    have hx := isSubstring_singleton.1 hsub
    obtain ⟨y, hy, heq⟩ := List.mem_map.1 hx
    have hyx : y = hCell M q cc := emb_inj M heq
    exact ⟨[hCell M q cc], hpat, isSubstring_singleton.2 (hyx ▸ hy)⟩
  · rintro ⟨subs, hmem, hsub⟩
    obtain ⟨q, cc, -, rfl⟩ := cookFinal_shape M hmem
    have hx := isSubstring_singleton.1 hsub
    refine ⟨[emb M (hCell M q cc)], ?_, ?_⟩
    · unfold guessFinal
      exact List.mem_map.2 ⟨[hCell M q cc], hmem, rfl⟩
    · exact isSubstring_singleton.2 (List.mem_map.2 ⟨_, hx, rfl⟩)

/-! ## The Γ-side transfers (T1/T2, PROVEN)

(T1 →) each covered window of an embedded row is covered by some
`guessCard`; a prelude card is refuted by `preludeCard_prem_ge` vs.
`emb_val_lt` on the window's first cell, so it is an `embCard`, and
`emb_inj` strips the embedding cell-wise. (T1 ←) map the covering card.
(T2) chain T1 with "the conclusion row of a covered step out of an
embedded row is itself embedded": every cell of the conclusion row lies in
some window, and embedded-card conclusions are `emb`-images. ⚠ T2 needs
`3 ≤ a.length` (surfaced by this proof): a row shorter than 3 has NO
windows, so `validStep` accepts *any* equal-length successor — including
non-embedded ones. All real rows have length ≥ 5. -/

theorem isPrefix_map_emb (M : FlatTM) :
    ∀ (xs ys : List (Fin (Sg M))),
      isPrefix (xs.map (emb M)) (ys.map (emb M)) → isPrefix xs ys
  | [], ys, _ => ⟨ys, rfl⟩
  | _ :: _, [], ⟨rest, heq⟩ => by simp at heq
  | x :: xs, y :: ys, ⟨rest, heq⟩ => by
      simp only [List.map_cons, List.cons_append, List.cons.injEq] at heq
      obtain ⟨hxy, htail⟩ := heq
      have hyx : y = x := emb_inj M hxy
      obtain ⟨rest', heq'⟩ := isPrefix_map_emb M xs ys ⟨rest, htail⟩
      exact ⟨rest', by rw [hyx, heq']; rfl⟩

/-- A prelude card cannot cover any window of an embedded row (band
mismatch on the window's first cell). -/
theorem prelude_no_cover_emb (M : FlatTM) {c : TCCCard (Fin (PSg M))}
    (hc : c ∈ preludeCards M) {a : List (Fin (Sg M))} {i : Nat}
    (hi : i < a.length) {b : List (Fin (PSg M))}
    (hcov : TCC.coversHead c ((a.map (emb M)).drop i) b) : False := by
  obtain ⟨rest, heq⟩ := hcov.1
  have h0 : ((a.map (emb M)).drop i)[0]? = some c.prem.cardEl1 := by
    rw [heq]; rfl
  rw [List.getElem?_drop, List.getElem?_map] at h0
  cases hai : a[i + 0]? with
  | none => rw [hai] at h0; simp at h0
  | some z =>
      rw [hai] at h0
      simp only [Option.map_some] at h0
      have hz : emb M z = c.prem.cardEl1 := Option.some.inj h0
      have hlt : c.prem.cardEl1.1 < Sg M := by rw [← hz]; exact z.2
      have hge := preludeCard_prem_ge M hc
      omega

/-- `coversHead` maps forward through the embedding. -/
theorem coversHead_emb_of (M : FlatTM) {c : TCCCard (Fin (Sg M))}
    {x y : List (Fin (Sg M))} (h : TCC.coversHead c x y) :
    TCC.coversHead (embCard M c) (x.map (emb M)) (y.map (emb M)) := by
  obtain ⟨⟨r1, h1⟩, ⟨r2, h2⟩⟩ := h
  refine ⟨⟨r1.map (emb M), ?_⟩, ⟨r2.map (emb M), ?_⟩⟩
  · rw [h1, List.map_append]; rfl
  · rw [h2, List.map_append]; rfl

/-- `coversHead` inverts through the embedding. -/
theorem coversHead_emb_inv (M : FlatTM) {c : TCCCard (Fin (Sg M))}
    {x y : List (Fin (Sg M))}
    (h : TCC.coversHead (embCard M c) (x.map (emb M)) (y.map (emb M))) :
    TCC.coversHead c x y := by
  obtain ⟨h1, h2⟩ := h
  have h1' : isPrefix ((c.prem : List (Fin (Sg M))).map (emb M))
      (x.map (emb M)) := h1
  have h2' : isPrefix ((c.conc : List (Fin (Sg M))).map (emb M))
      (y.map (emb M)) := h2
  exact ⟨isPrefix_map_emb M _ _ h1', isPrefix_map_emb M _ _ h2'⟩

/-- **T1 (Γ-step band transfer).** On embedded rows the combined card set
licenses exactly the deterministic core's steps. -/
theorem validStep_emb (M : FlatTM) (a b : List (Fin (Sg M))) :
    TCC.validStep (guessCards M) (a.map (emb M)) (b.map (emb M)) ↔
      TCC.validStep (cookCards M) a b := by
  constructor
  · rintro ⟨hlen, hcov⟩
    refine ⟨by simpa using hlen, ?_⟩
    intro i hi
    have hi' : i + 3 ≤ (a.map (emb M)).length := by
      rw [List.length_map]; omega
    obtain ⟨card, hmem, hcv⟩ := hcov i hi'
    rcases List.mem_append.1 hmem with hmem | hmem
    · obtain ⟨c0, hc0, rfl⟩ := List.mem_map.1 hmem
      have hda : (a.map (emb M)).drop i = (a.drop i).map (emb M) := by simp
      have hdb : (b.map (emb M)).drop i = (b.drop i).map (emb M) := by simp
      rw [hda, hdb] at hcv
      exact ⟨c0, hc0, coversHead_emb_inv M hcv⟩
    · exact absurd hcv (fun h => prelude_no_cover_emb M hmem (by omega) h)
  · rintro ⟨hlen, hcov⟩
    refine ⟨by simpa using hlen, ?_⟩
    intro i hi
    have hi' : i + 3 ≤ a.length := by
      rw [List.length_map] at hi; omega
    obtain ⟨card, hmem, hcv⟩ := hcov i hi'
    refine ⟨embCard M card,
      List.mem_append.2 (Or.inl (List.mem_map.2 ⟨card, hmem, rfl⟩)), ?_⟩
    have hda : (a.map (emb M)).drop i = (a.drop i).map (emb M) := by simp
    have hdb : (b.map (emb M)).drop i = (b.drop i).map (emb M) := by simp
    rw [hda, hdb]
    exact coversHead_emb_of M hcv

/-- A cell-wise Γ-band row is an embedded row. -/
theorem exists_preimage_map_emb (M : FlatTM) :
    ∀ (l : List (Fin (PSg M))), (∀ x ∈ l, x.1 < Sg M) →
      ∃ b : List (Fin (Sg M)), l = b.map (emb M)
  | [], _ => ⟨[], rfl⟩
  | x :: l, h => by
      obtain ⟨b, hb⟩ := exists_preimage_map_emb M l
        (fun y hy => h y (List.mem_cons_of_mem _ hy))
      refine ⟨⟨x.1, h x (by simp)⟩ :: b, ?_⟩
      simp only [List.map_cons, ← hb]
      rfl

/-- The conclusion row of a covered step out of an embedded row is itself
embedded (every cell lies in some window; prelude cards cannot fire). -/
theorem validStep_emb_row (M : FlatTM) {a : List (Fin (Sg M))}
    {b1 : List (Fin (PSg M))} (ha : 3 ≤ a.length)
    (h : TCC.validStep (guessCards M) (a.map (emb M)) b1) :
    ∃ b : List (Fin (Sg M)), b1 = b.map (emb M) := by
  obtain ⟨hlen, hcov⟩ := h
  rw [List.length_map] at hlen
  apply exists_preimage_map_emb
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hx
  set j := min i (a.length - 3) with hj
  have hj3 : j + 3 ≤ (a.map (emb M)).length := by
    rw [List.length_map]; omega
  obtain ⟨card, hmem, hcv⟩ := hcov j hj3
  rcases List.mem_append.1 hmem with hmem | hmem
  · obtain ⟨c0, hc0, rfl⟩ := List.mem_map.1 hmem
    obtain ⟨rest, heq⟩ := hcv.2
    have hgets : (b1.drop j)[i - j]? = b1[i]? := by
      rw [List.getElem?_drop]
      congr 1
      omega
    rw [heq] at hgets
    have hx' : b1[i]? = some b1[i] := List.getElem?_eq_getElem hi
    rw [hx'] at hgets
    rcases (by omega : i - j = 0 ∨ i - j = 1 ∨ i - j = 2) with h0 | h0 | h0 <;>
      rw [h0] at hgets
    · have hcell : b1[i] = emb M c0.conc.cardEl1 := (Option.some.inj hgets).symm
      rw [hcell]; exact (c0.conc.cardEl1).2
    · have hcell : b1[i] = emb M c0.conc.cardEl2 := (Option.some.inj hgets).symm
      rw [hcell]; exact (c0.conc.cardEl2).2
    · have hcell : b1[i] = emb M c0.conc.cardEl3 := (Option.some.inj hgets).symm
      rw [hcell]; exact (c0.conc.cardEl3).2
  · exact absurd hcv (fun hcv' => prelude_no_cover_emb M hmem (by omega) hcv')

/-- **T2 (Γ-chain band transfer, backward).** An embedded-start chain stays
embedded and projects to a deterministic-core chain. Needs `3 ≤ a.length`
(see the section note). -/
theorem relpower_emb (M : FlatTM) :
    ∀ (k : Nat) (a : List (Fin (Sg M))) (sf : List (Fin (PSg M))),
      3 ≤ a.length →
      relpower (TCC.validStep (guessCards M)) k (a.map (emb M)) sf →
      ∃ b, sf = b.map (emb M) ∧
        relpower (TCC.validStep (cookCards M)) k a b
  | 0, a, sf, _, h => by
      cases h with
      | refl => exact ⟨a, rfl, relpower.refl _⟩
  | k + 1, a, sf, ha, h => by
      cases h with
      | step hvs hrest =>
        obtain ⟨b, rfl⟩ := validStep_emb_row M ha hvs
        have hb : 3 ≤ b.length := by
          have hl := hvs.1
          simp only [List.length_map] at hl
          omega
        obtain ⟨bf, rfl, hrel⟩ := relpower_emb M k b sf hb hrest
        exact ⟨bf, rfl, relpower.step ((validStep_emb M a b).1 hvs) hrel⟩

/-- T2's forward companion (PROVEN modulo T1). -/
theorem relpower_emb_of (M : FlatTM) {k : Nat} {a b : List (Fin (Sg M))}
    (h : relpower (TCC.validStep (cookCards M)) k a b) :
    relpower (TCC.validStep (guessCards M)) k (a.map (emb M)) (b.map (emb M)) := by
  induction h with
  | refl a => exact relpower.refl _
  | step hstep _ ih => exact relpower.step ((validStep_emb M _ _).2 hstep) ih

/-! ## The prelude step (P1/P2) — sorried, the next top-down bite

Proof plan: row 0 has statically known shape (`preludeRow`); windows are
pinned coordinate-wise like `freeze_validStep`'s. (P1) per window, pick the
prelude card whose resolutions match `cert`'s cells (`contigOK` holds since
`cert`'s resolution is `symbols* blanks*`). (P2) per cell, invert the
covering card via `preludeCard_shape` (premise-match pins the kind triple
to the actual one); define `cert` as the live-star prefix; contiguity from
the window-overlap argument (design decision 4); the head cell resolution
pins `initFlatConfig`'s state and the position-0 symbol. -/

/-- **P1 (the guess step, forward).** A valid certificate's resolution of
the prelude row is card-licensed and lands on the deterministic core's
initial row for `s ++ cert`. -/
theorem prelude_validStep_of_cert (M : FlatTM) (s : List Nat)
    (maxSize steps : Nat) (hs : list_ofFlatType M.sig s)
    (cert : List Nat) (hc : list_ofFlatType M.sig cert)
    (hlen : cert.length ≤ maxSize) :
    TCC.validStep (guessCards M) (preludeRow M s maxSize steps)
      ((confRow M (initFlatConfig M [s ++ cert])
        (guessWidth s maxSize steps)).map (emb M)) := by
  sorry

/-- **P2 (the prelude inversion).** Any licensed step out of the prelude
row is the resolution of a valid certificate. -/
theorem cert_of_prelude_validStep (M : FlatTM) (s : List Nat)
    (maxSize steps : Nat) (hs : list_ofFlatType M.sig s)
    (row1 : List (Fin (PSg M)))
    (h : TCC.validStep (guessCards M) (preludeRow M s maxSize steps) row1) :
    ∃ cert, list_ofFlatType M.sig cert ∧ cert.length ≤ maxSize ∧
      row1 = (confRow M (initFlatConfig M [s ++ cert])
        (guessWidth s maxSize steps)).map (emb M) := by
  sorry

/-! ## The headline (ASSEMBLED — proven from P1/P2/T1/T2/T3) -/

theorem list_ofFlatType_append {k : Nat} {xs ys : List Nat}
    (hx : list_ofFlatType k xs) (hy : list_ofFlatType k ys) :
    list_ofFlatType k (xs ++ ys) := by
  intro x hx'
  rcases List.mem_append.1 hx' with h | h
  · exact hx x h
  · exact hy x h

/-- **The S1 reduction's correctness target**: certificate existence for
`FlatSingleTMGenNP`'s acceptance clause ⟺ the guess tableau covers. The
hypotheses are exactly the (decidable) instance-validity guards of the
future witness — mirroring `cookTableau_correct`'s guarded-map pattern. -/
theorem guessTableau_correct (M : FlatTM) (s : List Nat) (maxSize steps : Nat)
    (hV : validFlatTM M) (hT : M.tapes = 1) (hs : list_ofFlatType M.sig s) :
    (∃ cert, list_ofFlatType M.sig cert ∧ isValidCert maxSize cert ∧
      acceptsFlatTM M [s ++ cert] steps = true) ↔
    FlatTCC.FlatTCCLang (guessTableau M s maxSize steps) := by
  constructor
  · rintro ⟨cert, hc, hlen, hacc⟩
    have hlen' : cert.length ≤ maxSize := hlen
    have hsc : list_ofFlatType M.sig (s ++ cert) := list_ofFlatType_append hs hc
    rw [acceptsFlatTM_eq_true_iff] at hacc
    obtain ⟨cfg_f, hexec, hh⟩ := hacc
    rw [execFlatTM_eq_some_runFlatTM (isValidFlatTapes_single M (s ++ cert) hT hsc)]
      at hexec
    have hbase : (s ++ cert).length ≤ s.length + maxSize := by
      rw [List.length_append]; omega
    obtain ⟨hrel, hfitf⟩ := relpower_of_run M (guessWidth s maxSize steps) hV
      steps 0 (initFlatConfig M [s ++ cert]) cfg_f
      (ConfFits_init M (s ++ cert) hV hsc)
      (by unfold guessWidth; omega) (by unfold guessWidth; omega) hexec hh
    have hfin : TCC.satFinal (cookFinal M) (confRow M cfg_f (guessWidth s maxSize steps)) :=
      satFinal_of_halt M _ hfitf
        (by have := hfitf.head_le; unfold guessWidth; omega) hh
    have hchain : relpower (TCC.validStep (guessCards M)) (steps + 1)
        (preludeRow M s maxSize steps)
        ((confRow M cfg_f (guessWidth s maxSize steps)).map (emb M)) :=
      relpower.step (prelude_validStep_of_cert M s maxSize steps hs cert hc hlen')
        (relpower_emb_of M hrel)
    have htcc : TCC.TCCLang (guessTableauTyped M s maxSize steps) :=
      ⟨guessTableauTyped_wellformed M s maxSize steps,
        ⟨_, hchain, (satFinal_emb M _).2 hfin⟩⟩
    refine ⟨FlatTCC.flattenTCC_wellformed htcc.1,
      ⟨FlatTCC.isValidFlattening_flattenTCC _, ?_⟩⟩
    simpa [guessTableau, FlatTCC.unflatten_flattenTCC] using htcc
  · rintro ⟨-, hval, htcc⟩
    have heq : FlatTCC.unflattenTCC (guessTableau M s maxSize steps) hval
        = guessTableauTyped M s maxSize steps := FlatTCC.unflatten_flattenTCC _
    rw [heq] at htcc
    obtain ⟨-, sf, hrel, hfin⟩ := htcc
    cases hrel with
    | step hvs hrest =>
      obtain ⟨cert, hc, hlen, rfl⟩ :=
        cert_of_prelude_validStep M s maxSize steps hs _ hvs
      obtain ⟨bf, rfl, hrelG⟩ := relpower_emb M steps _ sf
        (by rw [confRow_length]; unfold guessWidth; omega) hrest
      have hsc : list_ofFlatType M.sig (s ++ cert) := list_ofFlatType_append hs hc
      have hfinG : TCC.satFinal (cookFinal M) bf := (satFinal_emb M bf).1 hfin
      have hbase : (s ++ cert).length ≤ s.length + maxSize := by
        rw [List.length_append]; omega
      obtain ⟨cfg_f, hrun, hh⟩ := run_of_relpower M (guessWidth s maxSize steps)
        hV steps 0 (initFlatConfig M [s ++ cert]) bf
        (ConfFits_init M (s ++ cert) hV hsc)
        (by unfold guessWidth; omega) (by unfold guessWidth; omega) hrelG hfinG
      refine ⟨cert, hc, hlen, ?_⟩
      rw [acceptsFlatTM_eq_true_iff]
      refine ⟨cfg_f, ?_, hh⟩
      rw [execFlatTM_eq_some_runFlatTM (isValidFlatTapes_single M (s ++ cert) hT hsc)]
      exact hrun

end Complexity.Simulators
