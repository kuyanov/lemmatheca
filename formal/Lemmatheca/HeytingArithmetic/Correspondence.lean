import Lemmatheca.HeytingArithmetic.Computations

/-! Literal identification with the existing PA theory, followed by the proved
classical presentation correspondence. This does not use model completeness. -/
namespace Lemmatheca.ProofTheory.HeytingArithmetic
open _root_.FirstOrder _root_.FirstOrder.Language
open Lemmatheca.ProofTheory.FirstOrder.BoundedFormula
open Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction
noncomputable section

/-- The order in the displayed seven-axiom presentation. -/
def basicAxiom (i : Fin 7) : Sentence :=
  ![qSuccNeZero, qSuccInjective, qPredecessor, qAddZero, qAddSucc, qMulZero, qMulSucc] i

/-- Actual earlier sentence declarations in the matching order. -/
def earlierBasicAxiom (i : Fin 7) : LA.Sentence :=
  ![Lemmatheca.ModelTheory.ArithmeticTheories.qSuccNeZero,
    Lemmatheca.ModelTheory.ArithmeticTheories.qSuccInjective,
    Lemmatheca.ModelTheory.ArithmeticTheories.qPredecessor,
    Lemmatheca.ModelTheory.ArithmeticTheories.qAddZero,
    Lemmatheca.ModelTheory.ArithmeticTheories.qAddSucc,
    Lemmatheca.ModelTheory.ArithmeticTheories.qMulZero,
    Lemmatheca.ModelTheory.ArithmeticTheories.qMulSucc] i

theorem basicAxiom_toClassical (i : Fin 7) :
    (basicAxiom i).toClassical = earlierBasicAxiom i := by
  fin_cases i <;> simp [basicAxiom, earlierBasicAxiom, qSuccNeZero, qSuccInjective,
    qPredecessor, qAddZero, qAddSucc, qMulZero, qMulSucc, close_toClassical,
    exUnit_toClassical, toClassical, termEqual,
    Lemmatheca.ModelTheory.ArithmeticTheories.qSuccNeZero,
    Lemmatheca.ModelTheory.ArithmeticTheories.qSuccInjective,
    Lemmatheca.ModelTheory.ArithmeticTheories.qPredecessor,
    Lemmatheca.ModelTheory.ArithmeticTheories.qAddZero,
    Lemmatheca.ModelTheory.ArithmeticTheories.qAddSucc,
    Lemmatheca.ModelTheory.ArithmeticTheories.qMulZero,
    Lemmatheca.ModelTheory.ArithmeticTheories.qMulSucc]
  all_goals rfl

theorem basic_toClassical :
    Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.toClassical '' basic =
      Lemmatheca.ModelTheory.ArithmeticTheories.Q := by
  have hB : basic = Set.range basicAxiom := by
    ext A
    simp [basic, basicAxiom, Fin.exists_fin_succ, eq_comm]
  have hQ : Lemmatheca.ModelTheory.ArithmeticTheories.Q = Set.range earlierBasicAxiom := by
    ext A
    simp [Lemmatheca.ModelTheory.ArithmeticTheories.Q, earlierBasicAxiom, Fin.exists_fin_succ, eq_comm]
  rw [hB, ← Set.range_comp', hQ]
  congr 1
  funext i
  exact basicAxiom_toClassical i

/-- The specified full body is projected, with its finite parameters unchanged. -/
theorem inductionAxiom_toClassical {k} (A : Formula (Fin k ⊕ Unit)) :
    (inductionAxiom A).toClassical =
      Lemmatheca.ModelTheory.ArithmeticTheories.inductionAxiom A.toClassical := by
  simp only [inductionAxiom, close_toClassical, toClassical, allUnit_toClassical,
    base, next, toClassical_subst, Lemmatheca.ModelTheory.ArithmeticTheories.inductionAxiom]

theorem inductionTheory_toClassical :
    Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.toClassical '' inductionTheory =
      Lemmatheca.ModelTheory.ArithmeticTheories.inductionTheory := by
  ext θ
  constructor
  · rintro ⟨D, ⟨k, A, rfl⟩, rfl⟩
    exact ⟨k, A.toClassical, inductionAxiom_toClassical A⟩
  · rintro ⟨k, D, rfl⟩
    refine ⟨inductionAxiom (ofClassical D), ⟨k, ofClassical D, rfl⟩, ?_⟩
    rw [inductionAxiom_toClassical, toClassical_ofClassical]

/-- Equality of the actual axiom sets, not a hypothetical alternate PA. -/
theorem theory_toClassical :
    Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.toClassical '' theory =
      Lemmatheca.ModelTheory.ArithmeticTheories.PA := by
  rw [theory, Set.image_union, basic_toClassical, inductionTheory_toClassical]
  rfl

/-- Earlier PA derivability is Prop-valued; the reverse gives proof existence. -/
theorem classical_iff_PA (A : Sentence) :
    Provable true (∅ : Context Empty) A ↔
      Lemmatheca.MathematicalLogic.FirstOrderProofs.Derives
        Lemmatheca.ModelTheory.ArithmeticTheories.PA A.toClassical := by
  have hT : assumptions theory (∅ : Context Empty) = theory := by
    ext θ
    have he : (Empty.elim : Empty → Empty) = id := funext (fun x => x.elim)
    simp only [assumptions, liftTheory, Finset.coe_empty, Set.union_empty,
      Set.mem_image]
    constructor
    · rintro ⟨D, hD, hEq⟩
      rw [he, rename_id] at hEq
      exact hEq ▸ hD
    · intro hθ
      exact ⟨θ, hθ, by rw [he, rename_id]⟩
  change TheoryDerives true true LA (assumptions theory ∅) A ↔ _
  rw [hT]
  simpa only [theory_toClassical] using
    Lemmatheca.ProofTheory.FirstOrder.ClassicalPresentation.theory_full_iff theory A

/-- Each actual native HA axiom holds in the specified standard structure. -/
theorem nat_axiom_truth {A : Sentence} (hA : A ∈ theory) :
    @Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Holds LA Empty ℕ
      Lemmatheca.ModelTheory.ArithmeticTheories.natStructure A Empty.elim := by
  have hm : A.toClassical ∈ Lemmatheca.ModelTheory.ArithmeticTheories.PA := by
    rw [← theory_toClassical]
    exact Set.mem_image_of_mem _ hA
  have ht := Lemmatheca.ModelTheory.ArithmeticTheories.nat_models_PA.realize_of_mem A.toClassical hm
  apply (toClassical_realize A Empty.elim Fin.elim0).mp
  unfold _root_.FirstOrder.Language.Sentence.Realize _root_.FirstOrder.Language.Formula.Realize at ht
  convert ht using 1


/-- Finite support and native soundness transfer axiom truth to the conclusion. -/
theorem Certificate.sound {α : Type*} {Γ : Context α} {A : Formula α} {c : Bool}
    (p : Certificate c Γ A) (a : α → ℕ)
    (hΓ : ∀ B ∈ Γ, @Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Holds LA α ℕ
      Lemmatheca.ModelTheory.ArithmeticTheories.natStructure B a) :
    @Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Holds LA α ℕ
      Lemmatheca.ModelTheory.ArithmeticTheories.natStructure A a := by
  apply Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.TheoryProof.sound p a
  intro B hB
  rcases hB with hT | hB
  · obtain ⟨θ, hθ, rfl⟩ := hT
    have hh := nat_axiom_truth hθ
    unfold Holds Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.Realize at hh ⊢
    unfold rename Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst
    rw [realize_map]
    convert hh using 1
    funext x
    cases x with
    | inl e => exact e.elim
    | inr i => exact i.elim0
  · exact hΓ B hB

theorem consistent : ¬ Provable false (∅ : Context Empty) (.falsum : Sentence) := by
  rintro ⟨p⟩
  exact p.sound Empty.elim (by simp)

end
end Lemmatheca.ProofTheory.HeytingArithmetic
