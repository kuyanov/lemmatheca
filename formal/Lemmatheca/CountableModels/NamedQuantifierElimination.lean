import Lemmatheca.QuantifierElimination.QuantifierEliminationShared

/-! Native quantifier elimination after adjoining an arbitrary set of constant symbols. -/
namespace Lemmatheca.ModelTheory.CountableModels

open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic.FirstOrderSyntax
open Lemmatheca.ModelTheory.QuantifierElimination.Shared

private theorem qf_toFormula {L : Language} {α : Type} {n : ℕ}
    {φ : L.BoundedFormula α n} (h : φ.IsQF) : φ.toFormula.IsQF := by
  induction h with
  | falsum => exact .falsum
  | of_isAtomic ha =>
    cases ha with
    | equal t s => exact (BoundedFormula.IsAtomic.equal _ _).isQF
    | rel r ts => exact (BoundedFormula.IsAtomic.rel _ _).isQF
  | imp _ _ ih₁ ih₂ => exact ih₁.imp ih₂

private theorem qf_names {L : Language} {ι α : Type} {n : ℕ}
    {φ : L.BoundedFormula (ι ⊕ α) n} (h : φ.IsQF) :
    (BoundedFormula.constantsVarsEquiv.symm φ : L[[ι]].BoundedFormula α n).IsQF := by
  induction h with
  | falsum => exact .falsum
  | of_isAtomic ha =>
    cases ha with
    | equal t s => exact (BoundedFormula.IsAtomic.equal _ _).isQF
    | rel r ts => exact (BoundedFormula.IsAtomic.rel _ _).isQF
  | imp _ _ ih₁ ih₂ => exact ih₁.imp ih₂

private theorem finite_context_elimination {α : Type} (φ : binaryRelLanguage.Formula α) :
    ∃ ψ : binaryRelLanguage.Formula α, ψ.IsQF ∧ strictDloTheory.Iff φ ψ := by
  classical
  let e := Fintype.equivFin φ.freeVarFinset
  let θ := Formula.relabel e (φ.restrictFreeVar id)
  obtain ⟨χ, hχ, he⟩ := strictDlo_hasQuantifierElimination _ (pack θ)
  let g : Empty ⊕ Fin (Fintype.card φ.freeVarFinset) → α :=
    Sum.elim Empty.elim (fun i => (e.symm i).val)
  refine ⟨Formula.relabel g χ.toFormula, (qf_toFormula hχ).relabel _, ?_⟩
  intro M v xs
  have hxs : xs = default := Subsingleton.elim _ _
  subst xs
  rw [BoundedFormula.realize_iff]
  change φ.Realize v ↔ (Formula.relabel g χ.toFormula).Realize v
  rw [Formula.realize_relabel, BoundedFormula.realize_toFormula]
  have hx : (v ∘ g) ∘ Sum.inr = (v ∘ Subtype.val) ∘ e.symm := rfl
  have hy : (v ∘ g) ∘ Sum.inl = Empty.elim := Subsingleton.elim _ _
  rw [hx, hy, ← he.realize_bd_iff (v := Empty.elim)]
  rw [pack_realize, Formula.realize_relabel]
  have hv : ((v ∘ Subtype.val) ∘ e.symm) ∘ e = v ∘ Subtype.val := by
    funext a
    simp
  rw [hv]
  exact (BoundedFormula.realize_restrictFreeVar v (by simp)).symm

/-- Only the formula's finite support is used, even when the added-name set is arbitrary. -/
theorem expanded_dlo_formula_elimination {ι : Type}
    (U : (binaryRelLanguage[[ι]]).Theory)
    (hU : (binaryRelLanguage.lhomWithConstants ι).onTheory strictDloTheory ⊆ U)
    {n : ℕ} (φ : (binaryRelLanguage[[ι]]).Formula (Fin n)) :
    ∃ ψ : (binaryRelLanguage[[ι]]).Formula (Fin n), ψ.IsQF ∧ U.Iff φ ψ := by
  obtain ⟨ψ, hψ, he⟩ := finite_context_elimination (BoundedFormula.constantsVarsEquiv φ)
  refine ⟨BoundedFormula.constantsVarsEquiv.symm ψ, qf_names hψ, ?_⟩
  intro M v xs
  let : binaryRelLanguage.Structure M := (binaryRelLanguage.lhomWithConstants ι).reduct M
  let : M ⊨ strictDloTheory :=
    ((binaryRelLanguage.lhomWithConstants ι).onTheory_model strictDloTheory).mp
      (M.is_model.mono hU)
  rw [BoundedFormula.realize_iff]
  have hxs : xs = default := Subsingleton.elim _ _
  subst xs
  change BoundedFormula.Realize φ v default ↔
    BoundedFormula.Realize (BoundedFormula.constantsVarsEquiv.symm ψ) v default
  rw [← BoundedFormula.realize_constantsVarsEquiv,
    ← BoundedFormula.realize_constantsVarsEquiv,
    Equiv.apply_symm_apply]
  exact he.realize_bd_iff

end Lemmatheca.ModelTheory.CountableModels
