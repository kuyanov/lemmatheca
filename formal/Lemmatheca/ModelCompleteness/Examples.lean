import Lemmatheca.ModelCompleteness.ModelCompleteness

/-! One-point structures distinguish model completeness from sentence completeness. -/
namespace Lemmatheca.Entry.ModelCompleteness
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic.FirstOrderSyntax
open Lemmatheca.MathematicalLogic.FirstOrderSemantics
open Lemmatheca.ModelTheory.ModelCompleteness

universe w

/-- The theory saying that the nonempty domain contains at most one element. -/
def singletonTheory : binaryRelLanguage.Theory := {allPairEqual binaryRelLanguage}

/-- The sentence separating the empty and full binary relations on one point. -/
def diagonalRelation : binaryRelLanguage.Sentence :=
  (Relations.boundedFormula₂ BinaryRelationSymbol.rel
    (.var (.inr 0)) (.var (.inr 0))).all

/-- Both interpretations of the relation on a singleton satisfy the size axiom. -/
theorem point_models (b : Prop) :
    let := binaryRelStructure PUnit.{w + 1} (fun _ _ => b)
    PUnit.{w + 1} ⊨ singletonTheory := by
  let := binaryRelStructure PUnit.{w + 1} (fun _ _ => b)
  change PUnit.{w + 1} ⊨ singletonTheory
  constructor
  intro σ hσ
  have hσ' : σ = allPairEqual binaryRelLanguage := Set.mem_singleton_iff.mp hσ
  subst σ
  exact allPairEqual_realize.mpr inferInstance

/-- The separating sentence has exactly the chosen relation's truth value. -/
theorem diagonalRelation_point (b : Prop) :
    let := binaryRelStructure PUnit.{w + 1} (fun _ _ => b)
    (PUnit.{w + 1} ⊨ diagonalRelation) ↔ b := by
  let := binaryRelStructure PUnit.{w + 1} (fun _ _ => b)
  change (∀ _ : PUnit.{w + 1}, b) ↔ b
  simp

/-- Model completeness can hold without agreement on sentences. -/
theorem singleton_modelComplete : ModelComplete.{0, 0, w} singletonTheory := by
  apply modelComplete_of_subsingleton_models
  intro M
  apply (allPairEqual_realize (L := binaryRelLanguage) (M := M)).mp
  exact M.is_model.realize_of_mem _ (by simp [singletonTheory])

/-- The two one-point interpretations witness failure of completeness. -/
theorem singleton_not_complete : ¬ singletonTheory.IsComplete := by
  intro h
  rcases h.2 diagonalRelation with htrue | hfalse
  · let := binaryRelStructure PUnit.{1} (fun _ _ => False)
    let : PUnit.{1} ⊨ singletonTheory := point_models False
    exact (diagonalRelation_point False).mp (htrue.realize_sentence PUnit.{1})
  · let := binaryRelStructure PUnit.{1} (fun _ _ => True)
    let : PUnit.{1} ⊨ singletonTheory := point_models True
    have h₁ := hfalse.realize_sentence PUnit.{1}
    have h₂ := (diagonalRelation_point True).mpr True.intro
    exact h₁ h₂

/-- The existential assertion that there is a point different from the parameter. -/
def differentPoint : binaryRelLanguage.Formula (Fin 1) :=
  (BoundedFormula.equal (.var (.inr 0)) (.var (.inl 0))).not.ex

/-- The formula in the second question really has existential form. -/
theorem differentPoint_existential : differentPoint.IsExistential := by
  exact ((BoundedFormula.IsAtomic.equal _ _).isQF.not).isExistential.ex

/-- In a singleton the formula fails, while a two-point empty-relation extension satisfies it. -/
theorem differentPoint_one_two :
    (let := binaryRelStructure (Fin 1) (fun _ _ => False);
      ¬ differentPoint.Realize (fun _ => (0 : Fin 1))) ∧
    (let := binaryRelStructure (Fin 2) (fun _ _ => False);
      differentPoint.Realize (fun _ => (0 : Fin 2))) := by
  constructor
  · let := binaryRelStructure (Fin 1) (fun _ _ => False)
    simp [differentPoint, Formula.Realize, BoundedFormula.Realize, Term.realize, Fin.snoc]
  · let := binaryRelStructure (Fin 2) (fun _ _ => False)
    simp [differentPoint, Formula.Realize, BoundedFormula.Realize, Term.realize, Fin.snoc]

/-- The specified inclusion of the one-point empty relation into the two-point relation. -/
def oneToTwo :
    let := binaryRelStructure (Fin 1) (fun _ _ => False)
    let := binaryRelStructure (Fin 2) (fun _ _ => False)
    Fin 1 ↪[binaryRelLanguage] Fin 2 := by
  let := binaryRelStructure (Fin 1) (fun _ _ => False)
  let := binaryRelStructure (Fin 2) (fun _ _ => False)
  exact
    { toFun := fun _ => 0
      inj' := fun _ _ _ => Subsingleton.elim _ _
      map_fun' := by intro n f; exact f.elim
      map_rel' := by intro n R a; cases R; exact Iff.rfl }

/-- The larger structure is outside the model-complete singleton theory. -/
theorem two_points_not_model :
    let := binaryRelStructure (Fin 2) (fun _ _ => False)
    ¬ Fin 2 ⊨ singletonTheory := by
  let := binaryRelStructure (Fin 2) (fun _ _ => False)
  change ¬ Fin 2 ⊨ singletonTheory
  intro h
  have hs : Subsingleton (Fin 2) :=
    (allPairEqual_realize (L := binaryRelLanguage) (M := Fin 2)).mp (h.realize_of_mem _ (by simp [singletonTheory]))
  exact (by decide : (0 : Fin 2) ≠ 1) (hs.elim 0 1)

end Lemmatheca.Entry.ModelCompleteness
