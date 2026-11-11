import Lemmatheca.TwoSatisfiability.Graph
import Mathlib.Order.Extension.Linear
import Mathlib.Data.Fintype.Sort

namespace Lemmatheca.MathematicalLogic.TwoSatisfiability
open Lemmatheca.MathematicalLogic.Propositional
open Lemmatheca.MathematicalLogic.DpllSatisfiability (Cnf opposite Models Sat)
universe u
variable {α : Type u}


def IsRank (Γ : Cnf α) (r : Component Γ → ℕ) : Prop :=
  Function.Injective r ∧ Monotone r

theorem rank_exists [Fintype α] (Γ : Cnf α) :
    ∃ r : Component Γ → ℕ, IsRank Γ r ∧
      ∀ i, (∃ C, r C = i) ↔ i < Fintype.card (Component Γ) := by
  classical
  let : Fintype (LinearExtension (Component Γ)) := componentFintype Γ
  let e : LinearExtension (Component Γ) ≃o Fin (Fintype.card (Component Γ)) :=
    (monoEquivOfFin (LinearExtension (Component Γ)) rfl).symm
  let r : Component Γ → ℕ := fun C => (e C).val
  refine ⟨r, ⟨?_, ?_⟩, ?_⟩
  · intro C D h
    exact e.injective (Fin.ext h)
  · intro C D h
    exact e.monotone (toLinearExtension.monotone h)
  · intro i
    constructor
    · rintro ⟨C,rfl⟩
      exact (e C).isLt
    · intro hi
      refine ⟨e.symm ⟨i,hi⟩, ?_⟩
      change (e (e.symm ⟨i,hi⟩)).val = i
      rw [e.apply_symm_apply]

noncomputable def chosenRank [Fintype α] (Γ : Cnf α) : Component Γ → ℕ :=
  Classical.choose (rank_exists Γ)

theorem chosenRank_spec [Fintype α] (Γ : Cnf α) :
    IsRank Γ (chosenRank Γ) ∧
      ∀ i, (∃ C, chosenRank Γ C = i) ↔ i < Fintype.card (Component Γ) := by
  exact Classical.choose_spec (rank_exists Γ)

def orderedAssignment (Γ : Cnf α) (r : Component Γ → ℕ) : Valuation α :=
  fun p => decide (r (componentOf Γ ⟨p,false⟩) < r (componentOf Γ ⟨p,true⟩))

theorem assignment_truth (Γ : Cnf α) (r : Component Γ → ℕ)
    (hr : IsRank Γ r) (hc : Consistent Γ) (a : PropLiteral α) :
    orderedAssignment Γ r a.atom = a.positive ↔
      r (componentOf Γ (opposite a)) < r (componentOf Γ a) := by
  rcases a with ⟨p,b⟩
  have hne : r (componentOf Γ ⟨p,false⟩) ≠ r (componentOf Γ ⟨p,true⟩) := by
    intro h
    apply hc ⟨p,false⟩
    exact (component_eq Γ ⟨p,false⟩ ⟨p,true⟩).mp (hr.1 h)
  cases b with
  | false => simp [orderedAssignment, opposite]; omega
  | true => simp [orderedAssignment, opposite]

theorem assignment_propagates (Γ : Cnf α) (r : Component Γ → ℕ)
    (hr : IsRank Γ r) (hc : Consistent Γ) {a b : PropLiteral α}
    (h : Reach Γ a b) (ha : orderedAssignment Γ r a.atom = a.positive) :
    orderedAssignment Γ r b.atom = b.positive := by
  apply (assignment_truth Γ r hr hc b).mpr
  have ht := (assignment_truth Γ r hr hc a).mp ha
  have hab := hr.2 ((component_le Γ a b).mpr h)
  have hba := hr.2 ((component_le Γ (opposite b) (opposite a)).mpr
    ((reach_opposite Γ a b).mp h))
  exact lt_of_le_of_lt hba (lt_of_lt_of_le ht hab)

theorem ordered_model (Γ : Cnf α) (h2 : IsTwo Γ) (he : [] ∉ Γ)
    (hc : Consistent Γ) (r : Component Γ → ℕ) (hr : IsRank Γ r) :
    Models (orderedAssignment Γ r) Γ := by
  intro C hC
  have hlen := h2 C hC
  cases C with
  | nil => exact (he hC).elim
  | cons l rest =>
    cases rest with
    | nil =>
      refine ⟨l, by simp, ?_⟩
      by_contra hn
      apply hn
      apply assignment_propagates Γ r hr hc
        (Relation.ReflTransGen.single
          ((edge_spec Γ (opposite l) l).mpr (Or.inl ⟨l,hC,rfl,rfl⟩)))
      exact (opposite_truth _ l).mpr hn
    | cons m rest =>
      cases rest with
      | nil =>
        by_cases hl : orderedAssignment Γ r l.atom = l.positive
        · exact ⟨l, by simp, hl⟩
        · refine ⟨m, by simp, ?_⟩
          apply assignment_propagates Γ r hr hc
            (Relation.ReflTransGen.single
              ((edge_spec Γ (opposite l) m).mpr (Or.inr ⟨l,m,hC,Or.inl ⟨rfl,rfl⟩⟩)))
          exact (opposite_truth _ l).mpr hl
      | cons n rest => simp only [List.length_cons] at hlen; omega

theorem criterion [Fintype α] (Γ : Cnf α) (h2 : IsTwo Γ) :
    Sat Γ ↔ [] ∉ Γ ∧ Consistent Γ := by
  constructor
  · rintro ⟨v,hv⟩
    refine ⟨?_, ?_⟩
    · intro he
      simpa using hv [] he
    · intro a hm
      exact contradictory_component Γ a hm ⟨v,hv⟩
  · rintro ⟨he,hc⟩
    exact ⟨orderedAssignment Γ (chosenRank Γ),
      ordered_model Γ h2 he hc (chosenRank Γ) (chosenRank_spec Γ).1⟩

theorem one_way_forces_false (Γ : Cnf α) (v : Valuation α) (hv : Models v Γ)
    (a : PropLiteral α) (h : Reach Γ a (opposite a)) :
    v a.atom ≠ a.positive := by
  intro ha
  exact ((opposite_truth v a).mp (reach_truth Γ v hv h ha)) ha


end Lemmatheca.MathematicalLogic.TwoSatisfiability
