import Lemmatheca.MembershipModels.MembershipModels
import Lemmatheca.InterpretingTheories.InterpretingTheories

namespace Lemmatheca.SetTheory.MembershipModels
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic.FirstOrderSyntax
open Lemmatheca.MathematicalLogic.FirstOrderSemantics
open Lemmatheca.MathematicalLogic.InterpretingTheories
universe u v w z
noncomputable section

instance membership_isRelational : membershipLanguage.IsRelational :=
  fun _ => inferInstanceAs (IsEmpty Empty)

/-- All fixed parameters of the class formula can be names in the ambient language.
Only the domain variable remains free in `δ`. -/
def membershipData {K : Language.{u,v}} (δ : K.Formula Unit) (r : K.Relations 2) :
    InterpretationData membershipLanguage K where
  domain := δ
  functionGraph f := Empty.elim f
  relationFormula s := by
    cases s
    exact r.formula (fun i => .var i)

def relativize {K : Language.{u,v}} (δ : K.Formula Unit) (r : K.Relations 2)
    {α : Type z} (φ : membershipLanguage.Formula α) : K.Formula α :=
  (membershipData δ r).relational φ

/-- The selected structure has ordinary restricted membership, with no additional
graph witnesses and no alternative formula syntax. -/
theorem relativize_realize {K : Language.{u,v}} (δ : K.Formula Unit) (r : K.Relations 2)
    {M : Type w} [K.Structure M] {α : Type z}
    (φ : membershipLanguage.Formula α)
    (a : α → {x : M // δ.Realize (fun _ => x)}) :
    letI := binaryRelStructure {x : M // δ.Realize (fun _ => x)}
      (fun x y => Structure.RelMap r ![x.val,y.val])
    (relativize δ r φ).Realize (fun i => (a i).val) ↔ φ.Realize a := by
  let I := membershipData δ r
  have he : I.inducedStructure (I.relational_graphs (M := M)) =
      binaryRelStructure {x : M // δ.Realize (fun _ => x)}
        (fun x y => Structure.RelMap r ![x.val,y.val]) := by
    apply Structure.ext
    · funext n f
      exact Empty.elim f
    · funext n s xs
      cases s
      change (r.formula (fun i => .var i)).Realize (fun i => (xs i).val) =
        Structure.RelMap r ![(xs 0).val, (xs 1).val]
      simp only [Formula.realize_rel, Term.realize_var]
      congr 1
      funext i
      fin_cases i <;> rfl
  have h := I.realize_relational (I.relational_graphs (M := M)) φ a
  rw [he] at h
  exact h

abbrev setDomainLanguage := membershipLanguage[[Unit]]

def setDomainFormula : setDomainLanguage.Formula Unit :=
  ((membershipLanguage.lhomWithConstants Unit).onRelation BinaryRelationSymbol.rel).formula
    ![.var (), (membershipLanguage.con ()).term]

def setRelativize {α : Type z} (φ : membershipLanguage.Formula α) :
    setDomainLanguage.Formula α :=
  relativize setDomainFormula
    ((membershipLanguage.lhomWithConstants Unit).onRelation BinaryRelationSymbol.rel) φ

@[instance_reducible] def setDomainStructure (D : ZFSet.{w}) :
    setDomainLanguage.Structure ZFSet.{w} :=
  @Language.withConstantsStructure membershipLanguage ZFSet
    universeMembershipStructure Unit (constantsOn.structure (fun _ => D))

theorem setDomainFormula_realize (D x : ZFSet.{w}) :
    letI := setDomainStructure D
    setDomainFormula.Realize (fun _ => x) ↔ x ∈ D := by rfl

theorem setRelativize_realize (D : ZFSet.{w}) {α : Type z}
    (φ : membershipLanguage.Formula α) (a : α → D) :
    letI := actualMembershipStructure D
    let lhs := φ.Realize a
    letI := setDomainStructure D
    (setRelativize φ).Realize (fun i => (a i).val) ↔ lhs := by
  let := setDomainStructure D
  exact relativize_realize setDomainFormula
    ((membershipLanguage.lhomWithConstants Unit).onRelation BinaryRelationSymbol.rel) φ a

end
end Lemmatheca.SetTheory.MembershipModels
