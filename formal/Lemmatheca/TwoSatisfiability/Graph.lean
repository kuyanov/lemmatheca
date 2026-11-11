import Lemmatheca.DpllSatisfiability.DpllSatisfiability
import Mathlib.Order.Antisymmetrization
import Mathlib.Data.Fintype.Basic

/-! Finite 2-CNF implication graphs and their actual ordered model construction. -/
namespace Lemmatheca.MathematicalLogic.TwoSatisfiability
open Lemmatheca.MathematicalLogic.Propositional
open Lemmatheca.MathematicalLogic.DpllSatisfiability (Cnf opposite Models Sat)
universe u
variable {α : Type u}

def IsTwo (Γ : Cnf α) : Prop := ∀ C ∈ Γ, C.length ≤ 2

def edges (Γ : Cnf α) : List (PropLiteral α × PropLiteral α) :=
  Γ.flatMap fun C => match C with
    | [l] => [(opposite l,l)]
    | [l,m] => [(opposite l,m),(opposite m,l)]
    | _ => []

def Edge (Γ : Cnf α) (a b : PropLiteral α) : Prop := (a,b) ∈ edges Γ
abbrev Reach (Γ : Cnf α) := Relation.ReflTransGen (Edge Γ)
def Mutual (Γ : Cnf α) (a b : PropLiteral α) : Prop := Reach Γ a b ∧ Reach Γ b a

def literalEquiv : PropLiteral α ≃ α × Bool where
  toFun l := (l.atom,l.positive)
  invFun p := ⟨p.1,p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance literalFintype [Fintype α] : Fintype (PropLiteral α) :=
  Fintype.ofEquiv (α × Bool) literalEquiv.symm

instance edgeDecidable [DecidableEq α] (Γ : Cnf α) : DecidableRel (Edge Γ) :=
  fun _ _ => inferInstanceAs (Decidable (_ ∈ edges Γ))

theorem opposite_involution (a : PropLiteral α) : opposite (opposite a) = a := by
  cases a with
  | mk p b => cases b <;> rfl

theorem opposite_truth (v : Valuation α) (a : PropLiteral α) :
    v (opposite a).atom = (opposite a).positive ↔ ¬ v a.atom = a.positive := by
  cases a with
  | mk p b => cases b <;> cases hv : v p <;> simp [opposite, hv]

theorem unit_duplicate (v : Valuation α) (a : PropLiteral α) :
    Models v [[a]] ↔ Models v [[a,a]] := by
  simp [Models, TseitinEncoding.ListModels]

theorem edge_spec (Γ : Cnf α) (a b : PropLiteral α) :
    Edge Γ a b ↔
      (∃ l, [l] ∈ Γ ∧ a = opposite l ∧ b = l) ∨
      (∃ l m, [l,m] ∈ Γ ∧
        ((a = opposite l ∧ b = m) ∨ (a = opposite m ∧ b = l))) := by
  unfold Edge edges
  constructor
  · intro h
    obtain ⟨C, hC, hp⟩ := List.mem_flatMap.mp h
    cases C with
    | nil => simp at hp
    | cons l rest =>
      cases rest with
      | nil =>
        simp only [List.mem_singleton, Prod.mk.injEq] at hp
        exact Or.inl ⟨l, hC, hp.1, hp.2⟩
      | cons m rest =>
        cases rest with
        | nil =>
          simp at hp
          exact Or.inr ⟨l, m, hC, hp⟩
        | cons n rest => simp at hp
  · rintro (⟨l, hC, ha, hb⟩ | ⟨l, m, hC, h⟩)
    · rw [ha,hb]
      exact List.mem_flatMap.mpr ⟨[l], hC, by simp⟩
    · rcases h with ⟨ha,hb⟩ | ⟨ha,hb⟩
      · rw [ha,hb]
        exact List.mem_flatMap.mpr ⟨[l,m], hC, by simp⟩
      · rw [ha,hb]
        exact List.mem_flatMap.mpr ⟨[l,m], hC, by simp⟩

theorem edge_truth (Γ : Cnf α) (v : Valuation α) (hv : Models v Γ)
    {a b : PropLiteral α} (h : Edge Γ a b) (ha : v a.atom = a.positive) :
    v b.atom = b.positive := by
  rcases (edge_spec Γ a b).mp h with ⟨l,hC,hea,heb⟩ | ⟨l,m,hC,h⟩
  · rw [heb]
    simpa using hv [l] hC
  · have ht : v l.atom = l.positive ∨ v m.atom = m.positive := by
      simpa using hv [l,m] hC
    rcases h with ⟨hea,heb⟩ | ⟨hea,heb⟩
    · rw [hea] at ha
      rw [heb]
      exact ht.resolve_left ((opposite_truth v l).mp ha)
    · rw [hea] at ha
      rw [heb]
      exact ht.resolve_right ((opposite_truth v m).mp ha)

theorem reach_truth (Γ : Cnf α) (v : Valuation α) (hv : Models v Γ)
    {a b : PropLiteral α} (h : Reach Γ a b) (ha : v a.atom = a.positive) :
    v b.atom = b.positive := by
  induction h with
  | refl => exact ha
  | tail h e ih => exact edge_truth Γ v hv e ih

theorem edge_opposite (Γ : Cnf α) (a b : PropLiteral α) :
    Edge Γ a b ↔ Edge Γ (opposite b) (opposite a) := by
  have go : ∀ a b, Edge Γ a b → Edge Γ (opposite b) (opposite a) := by
    intro a b h
    rcases (edge_spec Γ a b).mp h with ⟨l,hC,ha,hb⟩ | ⟨l,m,hC,h⟩
    · rw [ha,hb,opposite_involution]
      exact (edge_spec Γ (opposite l) l).mpr (Or.inl ⟨l,hC,rfl,rfl⟩)
    · rcases h with ⟨ha,hb⟩ | ⟨ha,hb⟩
      · rw [ha,hb,opposite_involution]
        exact (edge_spec Γ (opposite m) l).mpr (Or.inr ⟨l,m,hC,Or.inr ⟨rfl,rfl⟩⟩)
      · rw [ha,hb,opposite_involution]
        exact (edge_spec Γ (opposite l) m).mpr (Or.inr ⟨l,m,hC,Or.inl ⟨rfl,rfl⟩⟩)
  refine ⟨go a b, fun h => ?_⟩
  simpa only [opposite_involution] using go (opposite b) (opposite a) h

theorem reach_opposite (Γ : Cnf α) (a b : PropLiteral α) :
    Reach Γ a b ↔ Reach Γ (opposite b) (opposite a) := by
  have go : ∀ a b, Reach Γ a b → Reach Γ (opposite b) (opposite a) := by
    intro a b h
    induction h with
    | refl => exact .refl
    | tail h e ih => exact ih.head ((edge_opposite Γ _ _).mp e)
  refine ⟨go a b, fun h => ?_⟩
  simpa only [opposite_involution] using go (opposite b) (opposite a) h

theorem mutual_opposite (Γ : Cnf α) (a b : PropLiteral α) :
    Mutual Γ a b → Mutual Γ (opposite a) (opposite b) := by
  intro h
  exact ⟨(reach_opposite Γ b a).mp h.2, (reach_opposite Γ a b).mp h.1⟩

/-- Type alias equips the actual literals with the reachability preorder. -/
def Vertex (_Γ : Cnf α) := PropLiteral α

instance vertexPreorder (Γ : Cnf α) : Preorder (Vertex Γ) where
  le := Reach Γ
  le_refl _ := .refl
  le_trans _ _ _ := Relation.ReflTransGen.trans

instance vertexFintype [Fintype α] (Γ : Cnf α) : Fintype (Vertex Γ) := literalFintype

def Component (Γ : Cnf α) := Antisymmetrization (Vertex Γ) (· ≤ ·)

noncomputable instance componentFintype [Fintype α] (Γ : Cnf α) : Fintype (Component Γ) :=
  by
    classical
    exact Quotient.fintype _

instance componentPartialOrder (Γ : Cnf α) : PartialOrder (Component Γ) :=
  inferInstanceAs (PartialOrder (Antisymmetrization (Vertex Γ) (· ≤ ·)))

def componentOf (Γ : Cnf α) (a : PropLiteral α) : Component Γ :=
  toAntisymmetrization (· ≤ ·) (a : Vertex Γ)

def componentOpp (Γ : Cnf α) : Component Γ → Component Γ :=
  Quotient.map (opposite : Vertex Γ → Vertex Γ) (mutual_opposite Γ)

theorem component_eq (Γ : Cnf α) (a b : PropLiteral α) :
    componentOf Γ a = componentOf Γ b ↔ Mutual Γ a b := by
  exact Quotient.eq

theorem component_le (Γ : Cnf α) (a b : PropLiteral α) :
    componentOf Γ a ≤ componentOf Γ b ↔ Reach Γ a b := by
  rfl

theorem component_opposite (Γ : Cnf α) (a : PropLiteral α) :
    componentOpp Γ (componentOf Γ a) = componentOf Γ (opposite a) := by
  rfl

theorem component_opposite_involution (Γ : Cnf α) (C : Component Γ) :
    componentOpp Γ (componentOpp Γ C) = C := by
  refine Quotient.inductionOn C ?_
  intro a
  change componentOf Γ (opposite (opposite a)) = componentOf Γ a
  exact congrArg (componentOf Γ) (opposite_involution (α := α) a)

theorem component_opposite_order (Γ : Cnf α) (C D : Component Γ) :
    C ≤ D ↔ componentOpp Γ D ≤ componentOpp Γ C := by
  refine Quotient.inductionOn₂ C D ?_
  intro a b
  exact reach_opposite Γ a b

def Consistent (Γ : Cnf α) : Prop := ∀ a, ¬ Mutual Γ a (opposite a)

theorem contradictory_component (Γ : Cnf α) (a : PropLiteral α)
    (h : Mutual Γ a (opposite a)) : ¬ Sat Γ := by
  rintro ⟨v,hv⟩
  by_cases ha : v a.atom = a.positive
  · exact ((opposite_truth v a).mp (reach_truth Γ v hv h.1 ha)) ha
  · exact ha (reach_truth Γ v hv h.2 ((opposite_truth v a).mpr ha))

theorem consistent_components (Γ : Cnf α) :
    Consistent Γ ↔ ∀ C : Component Γ, C ≠ componentOpp Γ C := by
  constructor
  · intro hc C
    refine Quotient.inductionOn C ?_
    intro a he
    apply hc a
    apply (component_eq Γ a (opposite a)).mp
    exact he.trans (component_opposite Γ a)
  · intro hc a hm
    apply hc (componentOf Γ a)
    exact ((component_eq Γ a (opposite a)).mpr hm).trans (component_opposite Γ a).symm


end Lemmatheca.MathematicalLogic.TwoSatisfiability
