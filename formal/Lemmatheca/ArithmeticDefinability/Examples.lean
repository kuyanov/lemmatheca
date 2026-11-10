import Lemmatheca.ArithmeticDefinability.Selection

namespace Lemmatheca.Entry.ArithmeticDefinability
open Lemmatheca.ComputabilityTheory UniversalComputation

noncomputable def leastWitnessRelation (x y : ℕ) : Prop :=
  y = 1 ∨ (y = 0 ∧ x ∈ haltingDiagonal)

noncomputable def leastWitness (x : ℕ) : ℕ := by
  classical
  exact if x ∈ haltingDiagonal then 0 else 1

theorem least_witness_relation_enumerable :
    REPred (fun p : ℕ × ℕ => leastWitnessRelation p.1 p.2) := by
  have h₁ : REPred (fun p : ℕ × ℕ => p.2 = 1) :=
    (Primrec.eq.comp Primrec.snd (Primrec.const 1)).computablePred.to_re
  have h₀ : REPred (fun p : ℕ × ℕ => p.2 = 0) :=
    (Primrec.eq.comp Primrec.snd (Primrec.const 0)).computablePred.to_re
  have hN := enumerable_union (h₁.comp Primrec.unpair.to_comp)
    (enumerable_inter (h₀.comp Primrec.unpair.to_comp)
      (haltingDiagonal_enumerable.comp (Primrec.fst.comp Primrec.unpair).to_comp))
  exact REPred.of_eq (hN.comp (Primrec₂.natPair.comp Primrec.fst Primrec.snd).to_comp)
    (fun p => by simp [leastWitnessRelation])

theorem constant_one_selection :
    Computable (fun _ : ℕ => 1) ∧ ∀ x, leastWitnessRelation x 1 := by
  exact ⟨Computable.const 1, fun _ => Or.inl rfl⟩

theorem least_witness_spec (x : ℕ) :
    leastWitnessRelation x (leastWitness x) ∧
      (∀ y, leastWitnessRelation x y → leastWitness x ≤ y) ∧
      (leastWitness x = 0 ↔ x ∈ haltingDiagonal) := by
  classical
  by_cases hx : x ∈ haltingDiagonal <;> simp [leastWitness, leastWitnessRelation, hx]

theorem least_witness_not_computable : ¬ Computable leastWitness := by
  intro hf
  apply haltingDiagonal_undecidable
  exact (Primrec.eq.decide.to_comp.comp hf (Computable.const 0)).computablePred.of_eq
    (fun x => (least_witness_spec x).2.2)

end Lemmatheca.Entry.ArithmeticDefinability
