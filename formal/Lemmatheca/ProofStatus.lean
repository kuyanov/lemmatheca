import Lean

open Lean Elab Command in
elab "#node_status " declaration:str : command => do
  let name := declaration.getString.toName
  let _ ← getConstInfo name
  let axioms ← collectAxioms name
  -- This excludes sorryAx, including sorry inherited from other declarations.
  let verified := axioms.all fun dependency =>
    dependency == ``propext || dependency == ``Classical.choice || dependency == ``Quot.sound
  let signature ← liftTermElabM <| PrettyPrinter.ppSignature name
  let module ← findModuleOf? name
  let ranges ← findDeclarationRanges? name
  let result := Json.mkObj [
    ("declaration", toJson declaration.getString),
    ("verified", toJson verified),
    ("signature", toJson signature.fmt.pretty),
    ("module", toJson (module.map Name.toString)),
    ("declaration_line", toJson (ranges.map (·.selectionRange.pos.line)))]
  logInfo s!"NODE_STATUS {result.compress}"
