import Lemmatheca.EnumerationReducibility.Degrees

namespace Lemmatheca.Entry.EnumerationReducibility
open Lemmatheca.ComputabilityTheory
open EnumerationReducibility
open UniversalComputation

theorem finite_degree_zero (F : Finset ℕ) : degree (F : Set ℕ) = zeroDegree := by
  apply (degree_eq_zero_iff _).mpr
  change REPred (fun n => n ∈ F)
  induction F using Finset.induction_on with
  | empty =>
    exact ComputablePred.to_re
      (show ComputablePred (fun n : ℕ => n ∈ (∅ : Finset ℕ)) from
        ⟨inferInstance,by simpa using (Computable.const false : Computable (fun _ : ℕ => false))⟩)
  | @insert a F ha ih =>
    exact REPred.of_eq (enumerable_union
      (Primrec.eq.comp Primrec.id (Primrec.const a)).computablePred.to_re ih)
      (fun n => by simp)

theorem no_uniform_complement : ¬ ∃ e, ∀ B : Set ℕ, operator e B = Bᶜ := by
  rintro ⟨e,he⟩
  have hx : 0 ∈ operator e ∅ := by rw [he]; simp
  have hy := operator_monotone (indexedRule e) (Set.empty_subset ({0} : Set ℕ)) hx
  change 0 ∈ operator e {0} at hy
  rw [he] at hy
  simp at hy

theorem halting_bottom : Equivalent UniversalComputation.haltingDiagonal ∅ := by
  exact (degree_eq_iff _ _).mp
    ((degree_eq_zero_iff haltingDiagonal).mpr haltingDiagonal_enumerable)

theorem halting_complement_gap :
    ¬ Reducible UniversalComputation.haltingDiagonalᶜ UniversalComputation.haltingDiagonal ∧
      TuringDegrees.Reducible UniversalComputation.haltingDiagonalᶜ UniversalComputation.haltingDiagonal := by
  constructor
  · rintro ⟨e,he⟩
    apply haltingDiagonal_complement_not_enumerable
    change REPred (fun n => n ∈ haltingDiagonalᶜ)
    rw [←he]
    exact output_enumerable (indexedRule e)
      ((jointCE_iff_index _).mpr ⟨e,fun _ _ => Iff.rfl⟩) haltingDiagonal haltingDiagonal_enumerable
  · exact (TuringDegrees.complement_equivalent haltingDiagonal).2

theorem halting_total_complement :
    Equivalent UniversalComputation.haltingDiagonalᶜ (totalInfo UniversalComputation.haltingDiagonal) := by
  exact ⟨(join_lower_bounds haltingDiagonal haltingDiagonalᶜ).2,
    (join_reducible_iff _ _ _).mpr
      ⟨ce_reducible_everywhere haltingDiagonal haltingDiagonal_enumerable _,reducible_refl _⟩⟩

def innerRules (n d : ℕ) : Prop :=
  (n = 2 ∧ d = 0) ∨ (n = 5 ∧ d = FiniteSequenceCoding.code [1,4])

def outerRules (n d : ℕ) : Prop := n = 7 ∧ d = FiniteSequenceCoding.code [2,5]

theorem cover_examples_enumerable : JointCE innerRules ∧ JointCE outerRules := by
  have hu : Primrec (fun z : ℕ => z.unpair.1) := Primrec.fst.comp Primrec.unpair
  have hv : Primrec (fun z : ℕ => z.unpair.2) := Primrec.snd.comp Primrec.unpair
  exact ⟨((Primrec.eq.comp hu (Primrec.const 2)).and (Primrec.eq.comp hv (Primrec.const 0)) |>.or
      ((Primrec.eq.comp hu (Primrec.const 5)).and
        (Primrec.eq.comp hv (Primrec.const (FiniteSequenceCoding.code [1,4]))))).computablePred.to_re,
    ((Primrec.eq.comp hu (Primrec.const 7)).and
      (Primrec.eq.comp hv (Primrec.const (FiniteSequenceCoding.code [2,5])))).computablePred.to_re⟩

theorem innerRules_output (B : Set ℕ) :
    operatorOf innerRules B = {n | n = 2 ∨ (n = 5 ∧ 1 ∈ B ∧ 4 ∈ B)} := by
  ext n
  simp [operatorOf,innerRules,finiteSet,or_and_right,exists_or,Set.subset_def,or_imp,forall_and]

theorem cover_example_output (B : Set ℕ) :
    operatorOf (CompositeRules outerRules innerRules) B = {n | n = 7 ∧ 1 ∈ B ∧ 4 ∈ B} := by
  rw [composite_operator,innerRules_output]
  ext n
  simp [operatorOf,outerRules,finiteSet]

theorem empty_outer_output (S : RuleRelation) (B : Set ℕ) :
    operatorOf (CompositeRules (constantRules {7}) S) B = {7} := by
  rw [composite_operator,constant_operator]

end Lemmatheca.Entry.EnumerationReducibility
