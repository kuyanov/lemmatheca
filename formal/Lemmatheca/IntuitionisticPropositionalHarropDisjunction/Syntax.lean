import Lemmatheca.IntuitionisticPropositionalCutElimination.Translations

/-! Native Harrop formulas and the exact finite allowed-context condition. -/
namespace Lemmatheca.ProofTheory.Intuitionistic.Harrop
open Lemmatheca.MathematicalLogic.Propositional
open PropFormula
universe u v
variable {α : Type u} {β : Type v}

/-- Implication inputs and native negation arguments are unrestricted. -/
def IsHarrop : PropFormula α → Prop
  | .atom _ | .falsum | .neg _ => True
  | .conj A B => IsHarrop A ∧ IsHarrop B
  | .impl _ B => IsHarrop B
  | .disj _ _ => False

/-- Every allowed assumption, not merely every used leaf, satisfies the grammar. -/
def ContextHarrop (Γ : Finset (PropFormula α)) : Prop := ∀ D ∈ Γ, IsHarrop D

theorem grammar_examples (p q r s : α) :
    IsHarrop (.impl (.disj (.atom p) (.atom q)) (.atom r)) ∧
      IsHarrop (.conj (.impl (.disj (.atom p) (.atom q)) (.atom r)) (.neg (.atom s))) ∧
      ¬ IsHarrop (.disj (.atom p) (.atom q)) ∧
      ¬ IsHarrop (.impl (.atom r) (.disj (.atom p) (.atom q))) := by
  simp [IsHarrop]

variable [DecidableEq α]

omit [DecidableEq α] in
theorem context_subset [DecidableEq α] {Γ Δ : Finset (PropFormula α)}
    (hΓ : ContextHarrop Γ) (hΔ : Δ ⊆ Γ) : ContextHarrop Δ := by
  intro D hD
  exact hΓ D (hΔ hD)

theorem context_insert {Γ : Finset (PropFormula α)} {D : PropFormula α}
    (hΓ : ContextHarrop Γ) (hD : IsHarrop D) : ContextHarrop (insert D Γ) := by
  intro E hE
  rcases Finset.mem_insert.mp hE with rfl | hE
  · exact hD
  · exact hΓ E hE

theorem context_conj {Γ : Finset (PropFormula α)} {X Y : PropFormula α}
    (hΓ : ContextHarrop Γ) (h : .conj X Y ∈ Γ) :
    ContextHarrop (insert X (insert Y Γ)) := by
  exact context_insert (context_insert hΓ (hΓ _ h).2) (hΓ _ h).1

theorem context_impl {Γ : Finset (PropFormula α)} {X Y : PropFormula α}
    (hΓ : ContextHarrop Γ) (h : .impl X Y ∈ Γ) :
    ContextHarrop (insert Y Γ) := by
  exact context_insert hΓ (hΓ (.impl X Y) h)

omit [DecidableEq α] in
theorem context_no_disjunction [DecidableEq α] {Γ : Finset (PropFormula α)} (hΓ : ContextHarrop Γ)
    (A B : PropFormula α) : .disj A B ∉ Γ := by
  intro h
  exact hΓ _ h

omit [DecidableEq α] in
/-- A restriction on the atom images, not a claim about arbitrary substitution. -/
theorem substitute_harrop (σ : α → PropFormula β) (hσ : ∀ a, IsHarrop (σ a))
    (H : PropFormula α) (hH : IsHarrop H) : IsHarrop (subst σ H) := by
  induction H <;> simp_all [subst, IsHarrop]

end Lemmatheca.ProofTheory.Intuitionistic.Harrop
