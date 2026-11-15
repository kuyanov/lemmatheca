import Lemmatheca.StableFormulasAndDefinabilityOfTypes.Definitions
import Lemmatheca.OrderPatternsAndStability.Equality

namespace Lemmatheca.ModelTheory.StableDefinability
open FirstOrder FirstOrder.Language
open Lemmatheca.ModelTheory.OrderPatternsAndStability
universe u v w
noncomputable section

/-- The same signed finite test, with parameter tuples restricted to the displayed set. -/
def IsLocalTypeOn {L : Language.{u,v}} {M : Type w} [L.Structure M] {n m : ℕ}
    (φ : L.Formula (Fin (n+m))) (A : Set M) (P : Set (Fin m → A)) : Prop :=
  ∀ F : Finset (Fin m → A), ∃ a : Fin n → M,
    ∀ b ∈ F, Truth φ a (fun i => (b i).val) ↔ b ∈ P

def equalityFormula : Language.empty.Formula (Fin (1+1)) :=
  (Term.var (0 : Fin 2)).equal (Term.var 1)

def pointPositive {M : Type w} (a : M) : Set (Fin 1 → M) := {b | b 0 = a}

def pointDefinition {M : Type w} (a : M) :
    Language.empty[[(Set.univ : Set M)]].Formula (Fin 1) :=
  OrderPatternsAndStability.Equality.coordinateNamed (Set.univ : Set M) 1 0
    ⟨a,Set.mem_univ _⟩

variable {M : Type w} [Language.empty.Structure M]

theorem equality_truth (a b : Fin 1 → M) :
    Truth equalityFormula a b ↔ a 0 = b 0 := by
  rfl

theorem equality_point_realized (a : M) (b : Fin 1 → M) :
    Truth equalityFormula (fun _ => a) b ↔ b ∈ pointPositive a := by
  rw [equality_truth]
  exact eq_comm

theorem equality_point_local (a : M) :
    IsLocalType equalityFormula (pointPositive a) := by
  intro F
  exact ⟨fun _ => a, fun b _ => equality_point_realized a b⟩

theorem equality_empty_local [Infinite M] :
    IsLocalType equalityFormula (∅ : Set (Fin 1 → M)) := by
  classical
  intro F
  obtain ⟨a,ha⟩ := (F.image (fun b => b 0)).finite_toSet.exists_notMem
  refine ⟨fun _ => a, fun b hb => ?_⟩
  rw [equality_truth]
  simp only [Set.mem_empty_iff_false, iff_false]
  intro he
  exact ha (Finset.mem_image.mpr ⟨b,hb,he.symm⟩)

theorem equality_local_classification (P : Set (Fin 1 → M))
    (hP : IsLocalType equalityFormula P) :
    P = ∅ ∨ ∃ a : M, P = pointPositive a := by
  classical
  by_cases he : P = ∅
  · exact Or.inl he
  · have hn : P.Nonempty := Set.nonempty_iff_ne_empty.mpr he
    obtain ⟨b,hb⟩ := hn
    refine Or.inr ⟨b 0, ?_⟩
    ext c
    change c ∈ P ↔ c 0 = b 0
    obtain ⟨a,ha⟩ := hP {b,c}
    have hba : a 0 = b 0 := (equality_truth a b).mp ((ha b (by simp)).mpr hb)
    constructor
    · intro hc
      exact ((equality_truth a c).mp ((ha c (by simp)).mpr hc)).symm.trans hba
    · intro hc
      apply (ha c (by simp)).mp
      exact (equality_truth a c).mpr (hba.trans hc.symm)

theorem equality_point_definition (a : M) (b : Fin 1 → M) :
    (pointDefinition a).Realize b ↔ b ∈ pointPositive a := by
  rfl

theorem equality_empty_omitted [Nonempty M] :
    ¬ ∃ a : Fin 1 → M, ∀ b : Fin 1 → M,
      Truth equalityFormula a b ↔ b ∈ (∅ : Set (Fin 1 → M)) := by
  rintro ⟨a,ha⟩
  exact (ha a).mp ((equality_truth a a).mpr rfl)

theorem equality_no_three_pattern (a b : Fin 3 → Fin 1 → M) :
    ¬ OrderPattern equalityFormula a b := by
  intro h
  have h01 : (a 0) 0 = (b 1) 0 :=
    (equality_truth (a 0) (b 1)).mp ((h 0 1).mpr (by decide))
  have h02 : (a 0) 0 = (b 2) 0 :=
    (equality_truth (a 0) (b 2)).mp ((h 0 2).mpr (by decide))
  have h12 : (a 1) 0 = (b 2) 0 :=
    (equality_truth (a 1) (b 2)).mp ((h 1 2).mpr (by decide))
  have h11 := (h 1 1).mp ((equality_truth (a 1) (b 1)).mpr
    (h12.trans (h02.symm.trans h01)))
  exact (lt_irrefl (1 : Fin 3)) h11

theorem equality_empty_not_local [Finite M] [Nonempty M] :
    ¬ IsLocalType equalityFormula (∅ : Set (Fin 1 → M)) := by
  intro h
  exact equality_empty_omitted (finite_local_realization equalityFormula ∅ h)

theorem singleton_positive_local (a : M) :
    IsLocalTypeOn equalityFormula ({a} : Set M) Set.univ := by
  intro F
  refine ⟨fun _ => a, fun b _ => ?_⟩
  rw [equality_truth]
  simp only [Set.mem_univ, iff_true]
  exact (Set.mem_singleton_iff.mp (b 0).property).symm

theorem singleton_negative_local [Infinite M] (a : M) :
    IsLocalTypeOn equalityFormula ({a} : Set M) ∅ := by
  obtain ⟨c,hc⟩ := exists_ne a
  intro F
  refine ⟨fun _ => c, fun b _ => ?_⟩
  rw [equality_truth]
  simp only [Set.mem_empty_iff_false, iff_false]
  intro he
  exact hc (he.trans (Set.mem_singleton_iff.mp (b 0).property))

theorem singleton_named_definitions (a : M) (b : ({a} : Set M)) :
    (OrderPatternsAndStability.Equality.coordinateNamed ({a} : Set M) 1 0
      ⟨a,Set.mem_singleton a⟩).Realize (fun _ => b.val) ∧
      ¬ (⊥ : Language.empty[[({a} : Set M)]].Formula (Fin 1)).Realize
        (fun _ => b.val) := by
  constructor
  · change b.val = a
    exact Set.mem_singleton_iff.mp b.property
  · simp only [Formula.realize_bot, not_false_eq_true]

/-- The two explicit templates use one parameter; its only possible value is the singleton. -/
theorem singleton_two_templates (a : M) :
    let A : Set M := {a}
    let z : Fin 1 → A := fun _ => ⟨a,Set.mem_singleton a⟩
    ∀ b : A,
      Truth equalityFormula (fun _ => b.val) (fun i => (z i).val) ∧
      ¬ Truth (⊥ : Language.empty.Formula (Fin (1+1)))
        (fun _ => b.val) (fun i => (z i).val) := by
  dsimp only
  intro b
  constructor
  · apply (equality_truth _ _).mpr
    exact Set.mem_singleton_iff.mp b.property
  · simp only [Truth, Formula.realize_bot, not_false_eq_true]

/-- A genuine native template has only one instance over a singleton parameter supply. -/
theorem no_singleton_template {L : Language.{u,v}} {D : Type w} [L.Structure D]
    (a : D) (r : ℕ) (ψ : L.Formula (Fin (1+r))) :
    ¬ ((∃ z : Fin r → ({a} : Set D), ∀ b : ({a} : Set D),
        Truth ψ (fun _ => b.val) (fun i => (z i).val)) ∧
      (∃ z : Fin r → ({a} : Set D), ∀ b : ({a} : Set D),
        ¬ Truth ψ (fun _ => b.val) (fun i => (z i).val))) := by
  rintro ⟨⟨z,hz⟩,⟨z',hz'⟩⟩
  have he : (fun i => (z i).val) = (fun i => (z' i).val) := by
    funext i
    exact (Set.mem_singleton_iff.mp (z i).property).trans
      (Set.mem_singleton_iff.mp (z' i).property).symm
  have hp := hz ⟨a,Set.mem_singleton a⟩
  rw [he] at hp
  exact hz' _ hp

end
end Lemmatheca.ModelTheory.StableDefinability
