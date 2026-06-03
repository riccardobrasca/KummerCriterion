import Lean
import BernoulliRegular

open Lean

/-! Companion to `unseen.lean`. Where `#unseen` lists the declarations that are
used *nowhere*, `#unusedBy foo` lists the declarations that are used *nowhere in
the proof of a single chosen declaration* `foo` — i.e. everything in the project
that `foo` does not depend on, directly or transitively.

Run it with `lake env lean unused_by.lean`. Edit the `#unusedBy` line at the
bottom to point at the declaration you care about. -/

partial def allDeclsIn (module : Name) : Elab.Command.CommandElabM (Array Name) := do
  let mFile ← findOLean module
  unless (← mFile.pathExists) do
    logError m!"object file '{mFile}' of module {module} does not exist"
  let (md, _) ← readModuleData mFile
  let decls ← md.constNames.filterM fun d =>
    return !(← d.isBlackListed) && !(`injEq).isSuffixOf d && !(`sizeOf_spec).isSuffixOf d
  return decls

def allFiles (env : Environment) : List Name :=
  (env.importGraph.foldl (fun xs k _ => if (`BernoulliRegular).isPrefixOf k then
    k :: xs else xs) []).mergeSort
    (toString · < toString ·)

def allDecls (env : Environment) : Elab.Command.CommandElabM NameSet :=
  (fun l => NameSet.ofList (l.map (fun a => a.toList)).flatten) <$>
    (List.mapM allDeclsIn (allFiles env))

/-- Every constant *declared in a project module* — including `private`
declarations (whose real names are `_private.…`) and auto-generated ones. This is
the set of names we are allowed to recurse through when chasing dependencies. -/
def projectConsts (env : Environment) : Elab.Command.CommandElabM NameSet := do
  let arrs ← (allFiles env).mapM fun module => do
    let mFile ← findOLean module
    if (← mFile.pathExists) then return (← readModuleData mFile).1.constNames else return #[]
  return arrs.foldl (fun s a => a.foldl (·.insert ·) s) ∅

/-- The transitive closure of the *project* declarations appearing in the type or
proof of one of the names in `pending`, accumulated into `used`.

We recurse only into project declarations — those in `proj`, i.e. declared in a
project module. This is lossless: mathlib and the package dependencies are
compiled without the project, so no declaration outside `proj` can mention one
inside it; hence every project declaration reachable from `foo` is reachable by a
path that stays inside `proj`.

Membership in `proj` is tested by a **set lookup, not a name prefix**. An earlier
version pruned on the `BernoulliRegular` prefix and was badly wrong: `private`
declarations are named `_private.…`, and helper lemmas often live under other
namespaces (e.g. `Nat`). A single such bridge — here the `private` Kummer lemma
`fermatLastTheoremFor_of_isRegularPrime_dvd` — hid its entire subtree (~2000
declarations) from the walk. -/
partial def usedBy (env : Environment) (proj : NameSet) :
    List Name → NameSet → NameSet
  | [], used => used
  | n :: rest, used =>
    if used.contains n then
      usedBy env proj rest used
    else
      let deps := match env.find? n with
        | some info => info.getUsedConstantsAsSet.foldl (init := []) fun acc x =>
            if proj.contains x then x :: acc else acc
        | none => []
      usedBy env proj (deps ++ rest) (used.insert n)

/-- The user-facing form of a name, stripping the `_private.<module>.<n>.` header
that the compiler attaches to `private` declarations. -/
def displayName (n : Name) : Name := (privateToUserName? n).getD n

/-- `#unusedBy foo` computes the list of declarations in the project that are
*not* used (directly or transitively) in the proof of `foo`, and stores it in
`docs/unused_by.txt`. `foo` itself, and everything its statement and proof
depend on, are excluded; what remains is everything in the repo that is
irrelevant to `foo`.

Only hand-written declarations are listed. Compiler-synthesised constants
(equation lemmas like `.eq_def`, congruence lemmas `.congr_simp`, `match_`/
`proof_` auxiliaries, recursors, and equation lemmas of core declarations that
happen to be attributed to a project module) are filtered out: a synthesised
constant has no source declaration range, whereas anything you actually wrote —
`def`/`theorem`/`instance`/… — does. The dependency walk in `usedBy` still
traverses *all* constants, so this filtering never hides a genuine dependency;
it only trims the reported list. -/
elab "#unusedBy " id:ident : command => do
  let target ← Elab.Command.liftCoreM <| Lean.Elab.realizeGlobalConstNoOverloadWithInfo id
  let env ← getEnv
  let timeStart ← IO.monoMsNow
  let proj ← projectConsts env
  let written ← (← allDecls env).toList.filterM fun d =>
    return (← findDeclarationRanges? d).isSome
  let used := usedBy env proj [target] ∅
  let unused := written.filter (fun d => !used.contains d)
  let display := (unused.map displayName).mergeSort (toString · < toString ·)
  IO.FS.withFile "docs/unused_by.txt" IO.FS.Mode.write (fun h => do
    for v in display do
      h.write (v.toString ++ "\n").toUTF8)
  let timeEnd ← IO.monoMsNow
  logInfo m!"{displayName target}: {unused.length} of {written.length} written \
    project declarations are unused in its proof; {written.length - unused.length} \
    are used. Operation took {(timeEnd - timeStart) / 1000}s"

-- Replace the declaration below with the `foo` you want to analyse, then rerun.
#unusedBy fermatLastTheoremFor_le100_of_ne_irregular
