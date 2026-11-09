import Lemmatheca.UniversalComputation.UniversalComputation

/-! Complement enumeration, first used to classify satisfiability codes. -/
namespace Lemmatheca.ComputabilityTheory.ComputableSeparation

def CoEnumerable (P : Set ℕ) : Prop := REPred (fun x => x ∉ P)

end Lemmatheca.ComputabilityTheory.ComputableSeparation
