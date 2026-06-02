import Lean
import BernoulliRegular

open Lean

partial def allDeclsIn (module : Name) : Elab.Command.CommandElabM (Array Name) := do
  let mFile ← findOLean module
  unless (← mFile.pathExists) do logError m!"missing {module}"
  let (md, _) ← readModuleData mFile
  md.constNames.filterM fun d =>
    return !(← d.isBlackListed) && !(`injEq).isSuffixOf d && !(`sizeOf_spec).isSuffixOf d

def allFiles (env : Environment) : List Name :=
  (env.importGraph.foldl (fun xs k _ => if (`BernoulliRegular).isPrefixOf k then
    k :: xs else xs) []).mergeSort (toString · < toString ·)

def allDecls (env : Environment) : Elab.Command.CommandElabM NameSet :=
  (fun l => NameSet.ofList (l.map (·.toList)).flatten) <$> List.mapM allDeclsIn (allFiles env)

/-- Full closure: follow every used constant, no pruning. -/
partial def closureAll (env : Environment) : List Name → NameSet → NameSet
  | [], used => used
  | n :: rest, used =>
    if used.contains n then closureAll env rest used
    else
      let deps := match env.find? n with
        | some info => info.getUsedConstantsAsSet.toList
        | none => []
      closureAll env (deps ++ rest) (used.insert n)

/-- Pruned closure: only follow `BernoulliRegular`-prefixed deps (current method). -/
partial def closurePruned (env : Environment) : List Name → NameSet → NameSet
  | [], used => used
  | n :: rest, used =>
    if used.contains n then closurePruned env rest used
    else
      let deps := match env.find? n with
        | some info => info.getUsedConstantsAsSet.foldl (init := []) fun acc x =>
            if (`BernoulliRegular).isPrefixOf x then x :: acc else acc
        | none => []
      closurePruned env (deps ++ rest) (used.insert n)

elab "#cmp " id:ident : command => do
  let target ← Elab.Command.liftCoreM <| Lean.Elab.realizeGlobalConstNoOverloadWithInfo id
  let env ← getEnv
  let projList := (← allDecls env).toList
  let t0 ← IO.monoMsNow
  let full := closureAll env [target] ∅
  let t1 ← IO.monoMsNow
  let pruned := closurePruned env [target] ∅
  let t2 ← IO.monoMsNow
  let usedFull := projList.filter (full.contains ·)
  let usedPruned := projList.filter (pruned.contains ·)
  let missed := usedFull.filter (fun d => !pruned.contains d)
  logInfo m!"project decls={projList.length}  fullClosure={full.toList.length} ({(t1-t0)}ms)  \
    prunedClosure={pruned.toList.length} ({(t2-t1)}ms)"
  logInfo m!"project decls USED — full={usedFull.length}   pruned={usedPruned.length}"
  logInfo m!"project decls reachable in full but MISSED by pruning: {missed.length}"
  logInfo m!"first missed: {missed.take 40}"

#cmp BernoulliRegular.fermatLastTheoremFor_le100_of_ne_irregular
