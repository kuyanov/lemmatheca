import Lemmatheca.EqualityFreeIntuitionisticFirstOrderPrimeHenkinTheories.Extensions
namespace Lemmatheca.Entry.EqualityFreeIntuitionisticFirstOrderPrimeHenkinTheories
open _root_.FirstOrder _root_.FirstOrder.Language
open Lemmatheca.ProofTheory.FirstOrder
open Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction
open Lemmatheca.ProofTheory.FirstOrder.PrimeHenkin
universe u v
noncomputable section
variable {L : Language.{u,v}}

def atom (P : L.Relations 1) (c : ℕ) : Fml L :=
  .rel P (fun _ => .var (.inl c))

def allNames (P : L.Relations 1) : Set (Fml L) := Set.range (atom P)

@[instance_reducible]
def singletonStructure (L : Language.{u,v}) : L.Structure PUnit where
  funMap := fun _ _ => PUnit.unit
  RelMap := fun _ _ => True

theorem atom_support (P : L.Relations 1) (c : ℕ) :
    (atom P c).EqualityFree ∧ (atom P c).freeVarFinset = {c} := by
  constructor
  · trivial
  · ext x
    simp [atom,Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.freeVarFinset,Term.varFinsetLeft]


theorem allNames_supported (P : L.Relations 1) (U : Set ℕ) :
    allNames P ⊆ eligible U ↔ U = Set.univ := by
  constructor
  · intro h
    apply Set.eq_univ_of_forall
    intro c
    have hc := (h (Set.mem_range_self c)).2 c
    exact hc ((atom_support P c).2.symm ▸ Finset.mem_singleton_self c)
  · rintro rfl A ⟨c,rfl⟩
    exact ⟨(atom_support P c).1,fun _ _ => Set.mem_univ _⟩


theorem allNames_no_universe (P : L.Relations 1) (U : Universe) :
    ¬ allNames P ⊆ eligible U.carrier := by
  intro h
  have he := (allNames_supported P U.carrier).mp h
  have hi := U.infinite_compl
  rw [he,Set.compl_univ] at hi
  exact hi Set.finite_empty


theorem allNames_model (P : L.Relations 1) :
    letI := singletonStructure L
    ∀ A ∈ allNames P, Holds A (fun _ : ℕ => PUnit.unit) := by
  rintro A ⟨c,rfl⟩
  trivial


theorem allNames_consistent (P : L.Relations 1) : ¬ Provable (allNames P) .falsum := by
  let _ : L.Structure PUnit.{1} := singletonStructure L
  rintro ⟨p⟩
  exact p.sound (fun _ => PUnit.unit) (allNames_model P)

end
end Lemmatheca.Entry.EqualityFreeIntuitionisticFirstOrderPrimeHenkinTheories
