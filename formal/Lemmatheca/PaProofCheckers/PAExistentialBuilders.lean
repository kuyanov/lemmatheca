import Lemmatheca.PaProofCheckers.PAExistentialChain

open Lemmatheca.MathematicalLogic Lemmatheca.ModelTheory Lemmatheca.ComputabilityTheory

namespace Lemmatheca.ProofTheory.PAComputations.ProofPrograms.CheckerPrograms
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic ArithmeticTheories ArithmeticRepresentability
open SyntaxPrograms FixedSyntaxPrograms
noncomputable section
universe u

/-- The same enumeration used by the shared literal `iExs (Fin k)` operation. -/
def witnessCount (k : ℕ) : ℕ := Classical.choose (Finite.exists_equiv_fin (Fin k))
def witnessOrder (k : ℕ) : Fin k ≃ Fin (witnessCount k) :=
  Classical.choice (Classical.choose_spec (Finite.exists_equiv_fin (Fin k)))

def existentialCode {r k : ℕ} (D : language.Formula (Fin r ⊕ Fin k)) : Program (r + k) :=
  .comp (substitution (D.iExs (Fin k))) (fun i => .proj (i.castAdd k))

def existentialWitnesses (r k : ℕ) : Program (r + k) :=
  list (List.ofFn (fun j : Fin (witnessCount k) =>
    Program.proj (((witnessOrder k).symm j).natAdd r)))

def existentialBuilder {r k : ℕ} (D : language.Formula (Fin r ⊕ Fin k))
    (positive : Program (r + k)) : Program (r + k) :=
  ternary (existentialPrefix (witnessCount k))
    (existentialCode D) (existentialWitnesses r k) positive

variable {M : Type u} [language.Structure M] [M ⊨ PA]

theorem modelFormulaCodeAt_free_relabel {α β : Type*} (name : β → M)
    (offset : ℕ) (f : α → β) (A : language.Formula α) :
    modelFormulaCodeAt name offset (A.relabel f) =
      modelFormulaCodeAt (name ∘ f) offset A := by
  rw [Formula.relabel, modelFormulaCodeAt_relabel, Nat.add_zero]
  rfl

theorem substitution_model_value {r : ℕ} (A : language.Formula (Fin r)) (x : Fin r → M) :
    (substitution A).value x =
      modelFormulaCodeAt (fun i => ProofPrograms.numeral.value ![x i]) 0 A := by
  simp only [substitution, formulaCode_model_value, numeralName, unary_value,
    Program.value_proj]

theorem existentialWitnesses_value (r k : ℕ) (x : Fin (r + k) → M) :
    (existentialWitnesses r k).value x =
      modelList (List.ofFn (fun j : Fin (witnessCount k) =>
        x (((witnessOrder k).symm j).natAdd r))) := by
  simp only [existentialWitnesses, list_value, List.map_ofFn]
  apply congrArg modelList
  apply congrArg List.ofFn
  funext j
  exact Program.value_proj _ x

/-- The fixed syntax compiler and the literal chosen witness order agree at
both ends of the concrete prefix traversal. -/
theorem existentialCode_value {r k : ℕ} (D : language.Formula (Fin r ⊕ Fin k))
    (x : Fin (r + k) → M) :
    (existentialCode D).value x =
      prefixTarget (D.relabel (Sum.map id (witnessOrder k)))
        (fun i => x (i.castAdd k))
        (fun j => x (((witnessOrder k).symm j).natAdd r)) 0 := by
  rw [existentialCode, Program.value_comp, substitution_model_value]
  simp only [Program.value_proj]
  change modelFormulaCodeAt _ 0
    ((BoundedFormula.relabel (Sum.map id (witnessOrder k)) D).exs) = _
  rw [modelFormulaCodeAt_iExs]
  simp only [prefixTarget, prefixMatrix, Nat.sub_zero, Nat.zero_add, modelFormulaCodeAt_free_relabel]
  congr 2
  funext i
  cases i with
  | inl i => rfl
  | inr i =>
    simp only [Function.comp_apply, Sum.map_inr, prefixName, Sum.elim_inr,
      Nat.not_lt_zero, ↓reduceIte, Nat.sub_zero]

theorem existentialMatrix_value {r k : ℕ} (D : language.Formula (Fin r ⊕ Fin k))
    (x : Fin (r + k) → M) :
    (substitution (D.relabel finSumFinEquiv)).value x =
      prefixMatrix (D.relabel (Sum.map id (witnessOrder k)))
        (fun i => x (i.castAdd k))
        (fun j => x (((witnessOrder k).symm j).natAdd r)) (witnessCount k) := by
  rw [substitution_model_value, prefixMatrix_last, modelFormulaCodeAt_free_relabel,
    modelFormulaCodeAt_free_relabel]
  congr 1
  funext i
  cases i with
  | inl i => simp only [Function.comp_apply, finSumFinEquiv_apply_left, Sum.map_inl,
      Sum.elim_inl, id_eq]
  | inr i => simp only [Function.comp_apply, finSumFinEquiv_apply_right, Sum.map_inr,
      Sum.elim_inr, Equiv.symm_apply_apply]

theorem certified_existentialBuilder {r k : ℕ} (E : Program 2)
    (D : language.Formula (Fin r ⊕ Fin k)) (positive : Program (r + k))
    (x : Fin (r + k) → M)
    (hp : Certified E (positive.value x) ((substitution (D.relabel finSumFinEquiv)).value x)) :
    Certified E ((existentialBuilder D positive).value x) ((existentialCode D).value x) := by
  rw [existentialBuilder, ternary_value, existentialWitnesses_value,
    existentialCode_value]
  apply certified_prefixTarget E _ _ _ _
  rwa [← existentialMatrix_value]

end
end Lemmatheca.ProofTheory.PAComputations.ProofPrograms.CheckerPrograms
