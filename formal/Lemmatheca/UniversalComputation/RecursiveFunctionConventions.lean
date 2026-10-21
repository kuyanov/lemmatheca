import Lemmatheca.MachinesAndComputationHistories.MachinesAndComputationHistories

/-! Finite vectors and curried binary computability use the same two inputs. -/
namespace Lemmatheca.ComputabilityTheory.RecursiveFunctionConventions
open PartialRecursiveFunctions MachinesAndComputationHistories

private def pairArgs (p : ℕ × ℕ) : Args 2 :=
  List.Vector.ofFn (Fin.cases p.1 (fun _ => p.2))

private theorem pairArgs_primitive : Primrec pairArgs := by
  exact Primrec.vector_ofFn (fun i => Fin.cases Primrec.fst (fun _ => Primrec.snd) i)

theorem binary_recursive_iff {f : ℕ → ℕ → Part ℕ} :
    Recursive (fun v : Args 2 => f (v.get 0) (v.get 1)) ↔ Partrec₂ f := by
  rw [recursive_iff_partrec]
  constructor
  · intro hf
    exact (hf.comp pairArgs_primitive.to_comp).of_eq fun _ => rfl
  · intro hf
    exact hf.comp
      (Primrec.vector_get.comp Primrec.id (Primrec.const 0)).to_comp
      (Primrec.vector_get.comp Primrec.id (Primrec.const 1)).to_comp

theorem binary_total_recursive_iff {f : ℕ → ℕ → ℕ} :
    TotalRecursive (lift (fun v : Args 2 => f (v.get 0) (v.get 1))) ↔ Computable₂ f := by
  change (Recursive (fun v : Args 2 => Part.some (f (v.get 0) (v.get 1))) ∧
    ∀ v : Args 2, (Part.some (f (v.get 0) (v.get 1))).Dom) ↔ _
  rw [show (∀ v : Args 2, (Part.some (f (v.get 0) (v.get 1))).Dom) ↔ True by simp]
  simp only [and_true]
  rw [binary_recursive_iff (f := fun x y => Part.some (f x y))]
  change Partrec (fun p : ℕ × ℕ => Part.some (f p.1 p.2)) ↔
    Partrec (PFun.lift (fun p : ℕ × ℕ => f p.1 p.2))
  rfl

end Lemmatheca.ComputabilityTheory.RecursiveFunctionConventions
