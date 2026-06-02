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

/-- The transitive closure of the *project* declarations that appear in the type
or proof of one of the names in `pending`, accumulated into `used`.

We only ever follow edges into project declarations (those with the
`BernoulliRegular` prefix). This is both faster and lossless for our purpose:
mathlib is compiled without the project, so no mathlib declaration can reference
a project one, hence every project declaration reachable from `foo` is reachable
by a path that stays inside the project. -/
partial def usedBy (env : Environment) : List Name → NameSet → NameSet
  | [], used => used
  | n :: rest, used =>
    if used.contains n then
      usedBy env rest used
    else
      let deps := match env.find? n with
        | some info => info.getUsedConstantsAsSet.foldl (init := []) fun acc x =>
            if (`BernoulliRegular).isPrefixOf x then x :: acc else acc
        | none => []
      usedBy env (deps ++ rest) (used.insert n)

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
  let written ← (← allDecls env).toList.filterM fun d =>
    return (← findDeclarationRanges? d).isSome
  let used := usedBy env [target] ∅
  let unused := written.filter (fun d => !used.contains d)
  IO.FS.withFile "docs/unused_by.txt" IO.FS.Mode.write (fun h => do
    for v in unused.mergeSort (toString · < toString ·) do
      h.write (v.toString ++ "\n").toUTF8)
  let timeEnd ← IO.monoMsNow
  logInfo m!"{target}: {unused.length} of {written.length} written project \
    declarations are unused in its proof; operation took {(timeEnd - timeStart) / 1000}s"

-- Replace the declaration below with the `foo` you want to analyse, then rerun.
#unusedBy BernoulliRegular.fermatLastTheoremFor_le100_of_ne_irregular
