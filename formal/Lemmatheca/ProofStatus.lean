import Lean

namespace Lemmatheca

open Lean Elab Command

-- Recognized axioms across all supported node allowances. The corpus build
-- applies each node's allowance separately; recognizing Choice does not permit
-- it for a node whose axioms array is empty.
def supportedProofAxiom (name : Name) : Bool :=
  name == ``propext || name == ``Classical.choice || name == ``Quot.sound

end Lemmatheca

open Lean Elab Command in
elab "#node_status " declaration:str : command => do
  let name := declaration.getString.toName
  let _ ← getConstInfo name
  let axioms := (← collectAxioms name).qsort Name.quickLt
  -- This excludes sorryAx, including sorry inherited from other declarations.
  let verified := axioms.all Lemmatheca.supportedProofAxiom
  let signature ← liftTermElabM <| PrettyPrinter.ppSignature name
  let module ← findModuleOf? name
  let ranges ← findDeclarationRanges? name
  let result := Json.mkObj [
    ("declaration", toJson declaration.getString),
    ("verified", toJson verified),
    -- The corpus build applies each node's declared mathematical assumptions.
    ("lean_axioms", toJson (axioms.map Name.toString)),
    ("signature", toJson signature.fmt.pretty),
    ("module", toJson (module.map Name.toString)),
    ("declaration_line", toJson (ranges.map (·.selectionRange.pos.line)))]
  logInfo s!"NODE_STATUS {result.compress}"
