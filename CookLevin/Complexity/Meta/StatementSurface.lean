import Lean

/-! # `#assert_statement_surface` — *what a reviewer must read*, as a BUILD-TIME fact

## Why this file exists (top-down, 2026-08-06)

`#assert_axioms_clean` (see `Meta/AxiomGate.lean`) proves the headline is
**proved** — from nothing but `propext`, `Classical.choice` and `Quot.sound`.
It says nothing about what the headline *means*. A theorem can be impeccably
proved and still be about the wrong thing, and the only defence against that is
a human reading the definitions the statement is built from.

The README has always told a reviewer which definitions those are. Until now
that list was a **claim in prose**: nothing checked it was complete, and nothing
would notice if a later session slipped another definition into the statement.
For a development whose whole thesis is "you should not have to trust us", a
hand-maintained list of what you have to trust is the wrong shape.

This command turns it into a typechecking obligation:

```
#assert_statement_surface CookLevinHonest.CookLevinStr =>
  Complexity.Lang.NPcompleteStr
  …
```

*fails elaboration* — i.e. **breaks `lake build`** — unless the set of
**this repository's own constants** reachable from the *statement* (the type) of
the named theorem is **exactly** the listed set. Not a subset: exactly. So the
list cannot silently grow (a new definition sneaking into the trusted surface)
and cannot silently rot (a listed name that is no longer used).

## What "reachable from the statement" means, precisely

Start from the constants occurring in the theorem's **type**. Repeatedly:

* a constant declared **outside** this repository — Lean core, `Std`, Mathlib —
  is a leaf. We do not look inside it. That is the trust boundary this whole
  exercise is drawing: those are checked by their own communities, ours are not;
* a constant declared **inside** this repository (module under the `Complexity`
  root) is added to the surface, and we descend into its **type**, into its
  **value** if it is a definition, and into its **constructors** if it is an
  inductive type. Theorem *proofs* are not descended into — a proof cannot
  change what a statement means (and that it is a *correct* proof is
  `#assert_axioms_clean`'s job, not this one's).

The fixed point is the complete set of definitions written here that determine
what the theorem says. Read them and you have read the statement; read nothing
else and you have missed nothing.

## The reported list vs. the raw closure

The raw closure contains compiler-generated declarations — recursors,
`casesOn`, `noConfusion`, match auxiliaries, equation lemmas. Reporting them
would bury the list a human is supposed to read, so they are filtered out. The
filter is **not** taken on trust: every filtered name must either be
`Name.isInternalDetail` (Lean's own notion of "not user-facing") or have a
strict prefix that *is* in the reported list — i.e. be an artifact mechanically
generated from a declaration the reviewer is already reading. A filtered name
that meets neither condition fails the command. Nothing can hide in the gap.

## What it does NOT do

It cannot tell you the statement is *interesting*. Three obligations sit
outside it, deliberately, and each has its own instrument:

* the reduction's `encodeIn`/`decodeOut` are **existentially quantified** by
  `reducesPolyMO'`, so they are not part of the statement's meaning at all —
  which is exactly why encoding honesty (risk S5) needs a separate gate,
  `Complexity/HonestyGate.lean`;
* that the hypothesis class is inhabited, and by something hard —
  `Complexity/NonVacuity.lean`;
* that `Op.cost` is a faithful stand-in for machine time —
  `Complexity/CostFaithfulness.lean`.

A green surface gate means: *this, and nothing else of ours, is what the words
of the theorem are made of.*
-/

open Lean Elab Command

namespace Complexity.Meta

/-- Is `n` declared in **this repository** — a module under the `Complexity`
root — rather than in Lean core, `Std` or Mathlib? Declarations elaborated in
the current file have no module index yet and count as local. -/
def isRepoLocal (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | none => true
  | some idx =>
      match env.header.moduleNames[idx.toNat]? with
      | none => false
      | some m => (`Complexity).isPrefixOf m

/-- The constants a declaration contributes to the closure: those of its type,
those of its value (definitions only — a theorem's proof cannot change what a
statement means), and an inductive's constructors. -/
def contributions (ci : ConstantInfo) : Array Name :=
  let fromType := ci.type.getUsedConstants
  let fromVal :=
    match ci with
    | .thmInfo _ => #[]
    | _ => match ci.value? with
           | some v => v.getUsedConstants
           | none => #[]
  let ctors :=
    match ci with
    | .inductInfo iv => iv.ctors.toArray
    | _ => #[]
  fromType ++ fromVal ++ ctors

/-- The least set of repository-local constants containing `todo` and closed
under `contributions`. -/
partial def closure (env : Environment) (seen : NameSet) : List Name → NameSet
  | [] => seen
  | n :: rest =>
    if seen.contains n then closure env seen rest
    else
      let seen := seen.insert n
      match env.find? n with
      | none => closure env seen rest
      | some ci =>
        let next := (contributions ci).toList.filter (isRepoLocal env)
        closure env seen (next ++ rest)

/-- Name components Lean generates mechanically from a parent declaration.
A name carrying one of these is an artifact of the elaborator, not something a
reviewer reads — but see `checkHidden`: it is only dropped once we have proven
its parent is on the reported list. -/
def generatedComponents : List Name :=
  [`rec, `recOn, `casesOn, `brecOn, `below, `ibelow, `binductionOn, `ndrec,
   `noConfusion, `noConfusionType, `inj, `injEq, `sizeOf_spec, `toCtorIdx,
   `ofNat, `mk]

/-- Names not shown to a reviewer: Lean's own internal details, plus the
mechanically generated companions of a declaration. -/
def isGenerated (n : Name) : Bool :=
  n.isInternalDetail || n.components.any (generatedComponents.contains ·)

/-- Every strict prefix of `n`, longest first. -/
def strictPrefixes : Name → List Name
  | .anonymous => []
  | .str p _ => p :: strictPrefixes p
  | .num p _ => p :: strictPrefixes p

/-- **The filter's own soundness check.** A name removed from the report must be
either one of Lean's internal details, or generated from a declaration that *is*
on the report — otherwise it would be a genuine part of the trusted surface that
the report hides. Returns the offenders. -/
def checkHidden (reported : NameSet) (hidden : List Name) : List Name :=
  hidden.filter fun n =>
    !n.isInternalDetail && !(strictPrefixes n).any reported.contains

/-- The reported surface of `root`: the repository-local closure of its type,
minus the compiler-generated companions. Also returns the raw closure size and
the names the filter dropped. -/
def surfaceOf (env : Environment) (root : Name) : Option (List Name × Nat × List Name) :=
  match env.find? root with
  | none => none
  | some ci =>
    let roots := ci.type.getUsedConstants.toList.filter (isRepoLocal env)
    let all := (closure env {} roots).toList
    let reported := all.filter (fun n => !isGenerated n)
    let sorted := reported.mergeSort (fun a b => a.toString ≤ b.toString)
    some (sorted, all.length, all.filter isGenerated)

/-- **`#print_statement_surface thm`** — the *reporting* instrument, in the same
relation to `#assert_statement_surface` as `probes/AxiomProbe.lean` is to
`Complexity/SoundnessGate.lean`: it says what the surface *is*, in paste-ready
form, instead of failing when it is not what you said. Use it when adding an
endpoint to `Complexity/StatementGate.lean` — and then *read* the list before
pasting it, because that reading is the entire point of the gate. -/
syntax (name := printStatementSurfaceStx)
  "#print_statement_surface " ident : command

@[command_elab printStatementSurfaceStx]
def elabPrintStatementSurface : CommandElab := fun stx => do
  let env ← getEnv
  let root ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo stx[1]
  let some (names, total, _) := surfaceOf env root
    | throwError m!"unknown constant '{root}'"
  logInfo <| names.foldl (init := m!"statement surface of '{root}': \
      {names.length} of {total}") fun acc n => acc ++ m!"{Format.line}  {n}"

/-- **`#assert_statement_surface thm => n₁ n₂ …`** — a build-time assertion that
the constants of *this repository* reachable from the **statement** of `thm` are
exactly `n₁ … nₖ`. Elaboration fails (breaking `lake build`) if the two sets
differ in either direction. See this file's header for what "reachable" means. -/
syntax (name := assertStatementSurfaceStx)
  "#assert_statement_surface " ident " => " ident* : command

@[command_elab assertStatementSurfaceStx]
def elabAssertStatementSurface : CommandElab := fun stx => do
  let env ← getEnv
  let root ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo stx[1]
  let some (reportedList, total, hidden) := surfaceOf env root
    | throwError m!"unknown constant '{root}'"
  let reported : NameSet := reportedList.foldl NameSet.insert {}
  -- The filter may not hide anything a reviewer would need to read.
  let hiddenBad := checkHidden reported hidden
  unless hiddenBad.isEmpty do
    throwError m!"statement-surface gate FAILED for '{root}': \
        the report filter would hide {hiddenBad.length} name(s) with no parent \
        on the report{Format.line}  {hiddenBad.take 10}"
  -- The declared list.
  let mut declared : NameSet := {}
  for id in stx[3].getArgs do
    let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
    declared := declared.insert n
  let missing := reportedList.filter (fun n => !declared.contains n)
  let extra := declared.toList.filter (fun n => !reported.contains n)
  unless missing.isEmpty && extra.isEmpty do
    let fmt (l : List Name) :=
      (l.mergeSort (fun a b => a.toString ≤ b.toString)).foldl
        (init := m!"") fun acc n => acc ++ m!"{Format.line}    {n}"
    throwError m!"statement-surface gate FAILED for '{root}'"
      ++ (if missing.isEmpty then m!"" else
            m!"{Format.line}  reachable from the statement but NOT listed \
               ({missing.length}) — the trusted surface GREW:" ++ fmt missing)
      ++ (if extra.isEmpty then m!"" else
            m!"{Format.line}  listed but NOT reachable ({extra.length}) — \
               the list is stale:" ++ fmt extra)
      ++ m!"{Format.line}  ⚠ Do not just paste the new list in. A name appearing \
            here means the STATEMENT of the headline changed; say in \
            `README.md` what a reviewer now has to read, and why."
  logInfo m!"statement surface of '{root}': {reportedList.length} repository \
    definitions ({total} including generated companions) — list verified exact"

end Complexity.Meta
