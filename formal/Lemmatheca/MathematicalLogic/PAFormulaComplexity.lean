import Lemmatheca.MathematicalLogic.PAComputations
import Lemmatheca.MathematicalLogic.ArithmeticFormulaSubstitution

/-! Literal existential-prefix complexity, preserving the shared formula syntax. -/
namespace Lemmatheca.MathematicalLogic.PAComputations
open FirstOrder FirstOrder.Language
open ArithmeticTheories ArithmeticRepresentability FirstOrderProofs
noncomputable section

theorem SigmaOne.subst {α β : Type} {φ : language.Formula α} (h : SigmaOne φ)
    (σ : α → language.Term β) : SigmaOne (φ.subst σ) := by
  obtain ⟨k, δ, hδ, rfl⟩ := h
  rw [subst_iExs]
  exact ⟨k, δ.subst (underSubst σ), hδ.subst _, rfl⟩

theorem SigmaOne.relabel {α β : Type} {φ : language.Formula α} (h : SigmaOne φ)
    (f : α → β) : SigmaOne (φ.relabel f) := by
  rw [← formula_subst_vars]
  exact h.subst (fun x => .var (f x))

private def partialExs {α : Type} (m : ℕ) :
    (n : ℕ) → language.BoundedFormula α (m + n) → language.BoundedFormula α m
  | 0, φ => φ
  | n + 1, φ => partialExs m n φ.ex

private theorem exs_partialExs {α : Type} (m n : ℕ)
    (φ : language.BoundedFormula α (m + n)) :
    (partialExs m n φ).exs = φ.exs := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (partialExs m n φ.ex).exs = φ.ex.exs
    exact ih φ.ex

private theorem relabel_exs {α β : Type} {m n : ℕ}
    (φ : language.BoundedFormula α n) (f : α → β ⊕ Fin m) :
    BoundedFormula.relabel f φ.exs = partialExs m n (φ.relabel f) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [BoundedFormula.exs, ih, BoundedFormula.relabel_ex, partialExs]

/-- Reindex a bounded matrix to invert the particular finite enumeration used
by `iExs`. This is equality of syntax, not merely equivalence in PA. -/
private theorem raw_matrix {α : Type} {n m : ℕ}
    (φ : language.BoundedFormula α n) (hφ : DeltaZero φ.toFormula)
    (e : Fin n ≃ Fin m) (hm : m = n) :
    ∃ δ : language.Formula (α ⊕ Fin n), DeltaZero δ ∧
      (BoundedFormula.relabel (Sum.map id e) δ).exs = φ.exs := by
  subst m
  let f : α ⊕ Fin n → α ⊕ Fin n := Sum.map id e.symm
  let f₀ : α ⊕ Fin n → (α ⊕ Fin n) ⊕ Fin 0 := Sum.inl ∘ f
  refine ⟨φ.toFormula.relabel f, hφ.relabel f, ?_⟩
  have hr : BoundedFormula.relabel (Sum.map id e)
      (BoundedFormula.relabel f₀ φ.toFormula) = φ := by
    have hh := bounded_relabel_comp (m := 0) (n := n) φ.toFormula f₀ (Sum.map id e)
    simp only [BoundedFormula.castLE_rfl] at hh
    have hf : BoundedFormula.relabelAux (Sum.map id e) 0 ∘ f₀ =
        (id : α ⊕ Fin n → α ⊕ Fin n) := by
      funext x
      cases x with
      | inl x => rfl
      | inr i =>
        simp [f₀, f, BoundedFormula.relabelAux]
        exact Fin.ext rfl
    rw [hf, relabel_toFormula] at hh
    exact hh
  exact congrArg BoundedFormula.exs hr

private theorem sigmaOne_of_raw {α : Type} {n : ℕ}
    (φ : language.BoundedFormula α n) (hφ : DeltaZero φ.toFormula) : SigmaOne φ.exs := by
  let e := Classical.choice (Classical.choose_spec (Finite.exists_equiv_fin (Fin n)))
  have hm : Classical.choose (Finite.exists_equiv_fin (Fin n)) = n := by
    simpa only [Fintype.card_fin] using (Fintype.card_congr e).symm
  obtain ⟨δ, hδ, heq⟩ := raw_matrix φ hφ e hm
  refine ⟨n, δ, hδ, ?_⟩
  exact heq.symm

private theorem raw_of_sigmaOne {α : Type} {φ : language.Formula α} (h : SigmaOne φ) :
    ∃ n : ℕ, ∃ δ : language.BoundedFormula α n, DeltaZero δ.toFormula ∧ φ = δ.exs := by
  obtain ⟨k, δ, hδ, rfl⟩ := h
  unfold Formula.iExs
  refine ⟨_, _, ?_, rfl⟩
  rw [toFormula_relabel]
  apply DeltaZero.relabel
  rw [toFormula_zero]
  exact hδ.relabel Sum.inl

theorem SigmaOne.iExs {α β : Type} [Finite β] {φ : language.Formula (α ⊕ β)}
    (h : SigmaOne φ) : SigmaOne (φ.iExs β) := by
  obtain ⟨n, δ, hδ, rfl⟩ := raw_of_sigmaOne h
  unfold Formula.iExs
  dsimp only
  rw [relabel_exs]
  rw [exs_partialExs (Classical.choose (Finite.exists_equiv_fin β)) n]
  apply sigmaOne_of_raw
  rw [toFormula_relabel]
  exact hδ.relabel _

end
end Lemmatheca.MathematicalLogic.PAComputations
