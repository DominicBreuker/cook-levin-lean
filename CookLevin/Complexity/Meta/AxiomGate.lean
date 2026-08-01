import Lean

/-! # `#assert_axioms_clean` — axiom hygiene as a BUILD-TIME obligation

## Why this file exists (top-down, 2026-08-02)

`#print axioms` is this project's main soundness instrument, and until now it
was an instrument a *human* had to run: `probes/AxiomProbe.lean` lives outside
the `lean_lib` root, so `lake build` never elaborated it. That made the two
facts a reader most needs — *nothing on the proof path uses `sorry`* and
*nothing on the proof path uses a bespoke axiom* — depend on somebody
remembering to run a probe, or on a CI step that (see `CookLevin/HANDOFF.md`)
was never actually pushed.

`sorry` is only a **warning** in Lean, so a green `lake build` proves neither.
This command closes that gap without any CI, any script and any shell grep:

```
#assert_axioms_clean CookLevinHonest.CookLevinStr
```

*fails elaboration* — i.e. **breaks `lake build`** — unless the transitive
axiom set of every listed constant is contained in

```
{propext, Classical.choice, Quot.sound}
```

`sorryAx` is not in that set, and `Lean.collectAxioms` walks a constant's
*statement* as well as its proof. So this also catches standing architecture
risk #7 (a `sorry` hidden inside a `def` that only appears in a theorem's
statement), which is exactly the failure mode `#print axioms` was introduced
here to detect and which no `grep` for `sorry` can see through an import.

## What it does NOT do

It cannot see an *encoding-honesty* defect — a `sorry`-free, axiom-clean but
vacuous definition (the S1/S2 defects this project actually had). That is risk
S5, and its instruments are `probes/HonestyAuditProbe.lean` plus the
`NPhardStr` statement. Never read a green gate as "the theorem is meaningful";
read it as "the theorem is *proved*, and proved from nothing but Lean's own
foundations".

## Usage

Add every new endpoint to `CookLevin/Complexity/SoundnessGate.lean` — that is
the swept list, it is part of the default build target, and it is the file a
reviewer should read to see what is claimed.
-/

open Lean Elab Command

namespace Complexity.Meta

/-- The axioms a declaration on this project's proof path may depend on:
Lean's own three. Anything else — above all `sorryAx` — is a regression. -/
def cleanAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- Throw unless `constName`'s transitive axiom set is inside `cleanAxioms`. -/
def assertAxiomsCleanOf (constName : Name) : CommandElabM Unit := do
  let axs ← collectAxioms constName
  let bad := axs.filter fun a => !cleanAxioms.contains a
  unless bad.isEmpty do
    let sorried := bad.contains ``sorryAx
    let hint :=
      if sorried then
        m!"`sorryAx`: this declaration — or something in its STATEMENT — uses `sorry`."
      else
        m!"a bespoke `axiom` reached the proof path; project policy is `def` + `sorry`."
    throwError m!"axiom gate FAILED for '{constName}'"
      ++ m!"{Format.line}  forbidden axioms: {bad.qsort Name.lt |>.toList}"
      ++ m!"{Format.line}  allowed: {cleanAxioms}"
      ++ m!"{Format.line}  ⚠ {hint}"

/-- **`#assert_axioms_clean f g h`** — a build-time assertion that each named
constant depends on no axioms beyond `propext`, `Classical.choice` and
`Quot.sound`. Elaboration fails (breaking `lake build`) otherwise. -/
syntax (name := assertAxiomsCleanStx) "#assert_axioms_clean " ident+ : command

@[command_elab assertAxiomsCleanStx]
def elabAssertAxiomsClean : CommandElab := fun stx => do
  for id in stx[1].getArgs do
    let cs ← liftCoreM <| realizeGlobalConstWithInfos id
    for c in cs do
      assertAxiomsCleanOf c

/-! ## The whole-library sweep

`#assert_axioms_clean` gates the endpoints a reader is pointed at. That leaves
one gap: a `sorry` in a declaration no gated endpoint happens to mention. From
a *reading* point of view such a `sorry` is harmless — it is not on the proof
path — but the project's claim is stronger than "the endpoints are clean", and
a reader should not have to take the endpoint list on trust.

`#assert_library_axiom_clean Complexity` closes it: it walks **every**
declaration of **every** imported module under the given root and asserts the
same property. Placed in a module that transitively imports the whole library,
a green `lake build` then means *no declaration anywhere in this development
uses `sorry` or a bespoke axiom* — which is the fact `lake build` alone cannot
establish, since `sorry` is only a warning.

The axiom sets of imported declarations are precomputed at module-export time
(`Lean.exportedAxiomsExt`), so the sweep is a lookup per declaration, not a
re-traversal. -/

/-- Modules whose axiom sets are deliberately allowed to be dirty — the
negative controls. Empty today; keep it that way if you can. -/
def sweepExceptions : List Name := []

/-- **`#assert_library_axiom_clean Complexity`** — every declaration in every
imported module under the root namespace is axiom-clean. Fails elaboration
(and so `lake build`) otherwise. -/
syntax (name := assertLibraryCleanStx) "#assert_library_axiom_clean " ident : command

@[command_elab assertLibraryCleanStx]
def elabAssertLibraryClean : CommandElab := fun stx => do
  let root := stx[1].getId
  let env ← getEnv
  let names := env.header.moduleNames
  let data := env.header.moduleData
  let mut offenders : Array (Name × Name) := #[]
  let mut nModules := 0
  let mut nDecls := 0
  for i in [0:names.size] do
    let mn := names[i]!
    if root.isPrefixOf mn && !sweepExceptions.contains mn then
      nModules := nModules + 1
      for declName in data[i]!.constNames do
        nDecls := nDecls + 1
        let axs ← collectAxioms declName
        if axs.any fun a => !cleanAxioms.contains a then
          offenders := offenders.push (mn, declName)
  unless offenders.isEmpty do
    let shown := offenders.toList.take 20
    throwError m!"library axiom gate FAILED under '{root}': \
        {offenders.size} declaration(s) depend on a forbidden axiom"
      ++ m!"{Format.line}  allowed: {cleanAxioms}"
      ++ m!"{Format.line}  offenders (first {shown.length}):"
      ++ (shown.foldl (init := m!"") fun acc (mn, d) =>
            acc ++ m!"{Format.line}    {d}  (in {mn})")
  logInfo m!"axiom gate: {nDecls} declarations in {nModules} modules under \
    '{root}' are clean (no `sorry`, no bespoke axiom)"

end Complexity.Meta
