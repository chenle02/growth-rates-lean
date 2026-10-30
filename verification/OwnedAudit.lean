import Lean
open Lean

/-- Compiled with Lean alone; the mathematical modules are loaded as data at runtime. -/
def inspectOwned (root : Name) (contracts : Array Name) : CoreM Unit := do
  let env := (← getEnv).setExporting false
  let mut rows : Array (Name × Name) := #[]
  for (name, _) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let mod := env.header.moduleNames[idx.toNat]!
      if root.isPrefixOf mod then rows := rows.push (mod, name)
  for (mod, name) in rows.qsort (fun a b => Name.lt a.2 b.2) do
    let some info := env.find? name | throwError "missing owned constant"
    let kind := match info with
      | .thmInfo _ => "theorem" | .defnInfo _ => "definition"
      | .opaqueInfo _ => "opaque" | .axiomInfo _ => "axiom"
      | .quotInfo _ => "quotient" | .inductInfo _ => "inductive"
      | .ctorInfo _ => "constructor" | .recInfo _ => "recursor"
    let unsafeDecl := match info with
      | .defnInfo v => v.safety != DefinitionSafety.safe
      | .opaqueInfo v => v.isUnsafe
      | .recInfo v => v.isUnsafe
      | .inductInfo v => v.isUnsafe
      | .ctorInfo v => v.isUnsafe
      | _ => false
    let axs ← collectAxioms name
    let returnsProp := match info.type.getForallBody with
      | .sort .zero => true
      | _ => false
    let body := if contracts.contains name then
      match info with | .defnInfo v => reprStr v.value | _ => ""
      else ""
    let fullBody := match info with
      | .defnInfo v => reprStr v.value
      | .thmInfo v => reprStr v.value
      | .opaqueInfo v => reprStr v.value
      | .recInfo v => reprStr (v.rules.map fun (r : RecursorRule) => (r.ctor.toString, r.nfields, reprStr r.rhs))
      | _ => ""
    let row := Json.mkObj [
      ("name", toJson name.toString), ("module", toJson mod.toString),
      ("kind", toJson kind), ("level_params", toJson (info.levelParams.map Name.toString)), ("unsafe", toJson unsafeDecl),
      ("axioms", toJson (axs.map Name.toString)), ("returns_prop", toJson returnsProp),
      ("type_repr", toJson (reprStr info.type)),
      ("body_repr", toJson fullBody),
      ("definition_body_repr", toJson body)]
    liftM (m := CoreM) <| IO.println ("OWNED-DECL " ++ row.compress)
  let imports := env.header.moduleNames.filter fun m =>
    root.isPrefixOf m
  liftM (m := CoreM) <| IO.println ("OWNED-IMPORTS " ++ (toJson (imports.map Name.toString)).compress)
  liftM (m := CoreM) <| IO.println ("OWNED-DONE " ++ toString rows.size)

def main (args : List String) : IO UInt32 := do
  let [config] := args | throw <| IO.userError "expected scope configuration"
  let cfg ← IO.ofExcept <| Json.parse (← IO.FS.readFile config)
  let root ← IO.ofExcept <| cfg.getObjValAs? String "root_module"
  let names ← IO.ofExcept <| cfg.getObjValAs? (Array String) "contracts"
  initSearchPath (← findSysroot)
  let env ← importModules #[{module := root.toName, importAll := true}]
    {} (loadExts := false) (level := .private)
  let ctx : Core.Context := {fileName := "<owned-statement-audit>", fileMap := default}
  discard <| (inspectOwned root.toName (names.map String.toName)).toIO ctx {env := env}
  return 0
