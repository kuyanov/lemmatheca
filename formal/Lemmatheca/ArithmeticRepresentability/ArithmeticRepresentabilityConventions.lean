import Lemmatheca.ArithmeticRepresentability.ArithmeticRepresentability

open Lemmatheca.MathematicalLogic Lemmatheca.ModelTheory Lemmatheca.ComputabilityTheory

/-! The total recursive class already defined in the corpus agrees with the
library computability convention at every finite arity, including arity zero. -/
namespace Lemmatheca.ProofTheory.ArithmeticRepresentability
open Lemmatheca.MathematicalLogic
open PartialRecursiveFunctions
noncomputable section

theorem total_recursive_iff_computable {n : ℕ} (f : Args n → ℕ) :
    TotalRecursive (lift f) ↔ Computable f := by
  change (Recursive (fun v => Part.some (f v)) ∧
    ∀ v, (Part.some (f v)).Dom) ↔ _
  rw [MachinesAndComputationHistories.recursive_iff_partrec]
  simp only [Part.some_dom, implies_true, and_true]
  rfl

/-- The tuple coordinate maps are the corpus's actual finite-vector maps;
no fresh encoding of arities is introduced. -/
theorem finite_arity_total_recursive_iff {n : ℕ} (f : (Fin n → ℕ) → ℕ) :
    TotalRecursive (lift (fun v : Args n => f v.get)) ↔ Computable f := by
  constructor
  · intro hf
    have hpack : Primrec (fun x : Fin n → ℕ => List.Vector.ofFn x) :=
      Primrec.vector_ofFn (fun i => Primrec.fin_app.comp Primrec.id (Primrec.const i))
    have hc := (total_recursive_iff_computable (fun v : Args n => f v.get)).mp hf
    apply (hc.comp hpack.to_comp).of_eq
    intro x
    congr 1
    funext i
    exact List.Vector.get_ofFn x i
  · intro hf
    apply (total_recursive_iff_computable (fun v : Args n => f v.get)).mpr
    exact hf.comp Primrec.vector_get'.to_comp

end
end Lemmatheca.ProofTheory.ArithmeticRepresentability
