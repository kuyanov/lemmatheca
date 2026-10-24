import Lemmatheca.StronglyMinimalSets.Exchange
import Lemmatheca.StronglyMinimalSets.FiniteDimension
import Lemmatheca.DefinableAndAlgebraicClosure.Examples

namespace Lemmatheca.Entry.StronglyMinimalSets
open FirstOrder FirstOrder.Language
open Lemmatheca.ModelTheory.StronglyMinimalSets
open Lemmatheca.ModelTheory.Closures
open Lemmatheca.MathematicalLogic.FirstOrderSyntax
open Lemmatheca.MathematicalLogic.FirstOrderSemantics
universe w
noncomputable section

theorem equality_stronglyMinimalTheory :
    StronglyMinimalTheory Language.empty.infiniteTheory := by
  intro P
  let : Infinite P := (Language.empty.model_infiniteTheory_iff).mp P.is_model
  exact ⟨inferInstance,fun s hs =>
    (Lemmatheca.ModelTheory.QuantifierElimination.Shared.equality_definable_iff_finite_cofinite s).mp hs⟩

theorem equality_independent {M : Type w} [Language.empty.Structure M] [Infinite M]
    (A : Set M) :
    (aclPregeometry Language.empty.infiniteTheory equality_stronglyMinimalTheory
      (M := M)).Independent A := by
  intro a ha hcl
  change a ∈ acl Language.empty (A \ {a}) at hcl
  rw [(Lemmatheca.Entry.DefinableAndAlgebraicClosure.infinite_equality_closures (A \ {a})).2] at hcl
  exact hcl.2 rfl

theorem equality_finite_dimension {M : Type w} [Language.empty.Structure M] [Infinite M]
    (S : Finset M) :
    let P := aclPregeometry Language.empty.infiniteTheory equality_stronglyMinimalTheory (M := M)
    P.IsBasis (S : Set M) (S : Set M) ∧ ∃ hS : P.FinitelyGenerated (S : Set M),
      P.finiteDimension (S : Set M) hS = S.card := by
  classical
  let P := aclPregeometry Language.empty.infiniteTheory equality_stronglyMinimalTheory (M := M)
  have hcl (A : Set M) : P.cl A = A :=
    (Lemmatheca.Entry.DefinableAndAlgebraicClosure.infinite_equality_closures A).2
  have hb : P.IsBasis (S : Set M) (S : Set M) :=
    ⟨Set.Subset.refl _,equality_independent _,hcl _⟩
  have hg : P.FinitelyGenerated (S : Set M) := ⟨S,hcl _⟩
  exact ⟨hb,hg,P.finiteDimension_eq_card _ hg S hb⟩

def halfLineFormula : binaryRelLanguage.Formula (Fin 1 ⊕ Fin 1) :=
  Relations.formula₂ BinaryRelationSymbol.rel (.var (.inr 0)) (.var (.inl 0))

theorem dense_order_not_minimal {M : Type w} [LinearOrder M] [DenselyOrdered M]
    [NoMinOrder M] [NoMaxOrder M] [Nonempty M] :
    letI : binaryRelLanguage.Structure M := binaryRelStructure M (fun x y => x < y)
    (∀ a : M, fiber halfLineFormula (fun _ => a) = Set.Iio a ∧
      (Set.Iio a).Infinite ∧ (Set.Iio a)ᶜ.Infinite) ∧ ¬Minimal binaryRelLanguage M := by
  let : binaryRelLanguage.Structure M := binaryRelStructure M (fun x y => x < y)
  have hf (a : M) : fiber halfLineFormula (fun _ => a) = Set.Iio a := by
    ext x
    rfl

  have hc (a : M) : (Set.Iio a)ᶜ.Infinite := by
    exact (Set.Ioi_infinite a).mono (by intro x hx; exact not_lt.mpr (le_of_lt hx))
  refine ⟨fun a => ⟨hf a,Set.Iio_infinite a,hc a⟩,?_⟩
  intro hm
  obtain ⟨a⟩ := ‹Nonempty M›
  rcases (minimal_iff_fibers.mp hm).2 1 halfLineFormula (fun _ => a) with h | h
  · exact Set.Iio_infinite a (hf a ▸ h)
  · exact hc a (hf a ▸ h)

theorem dense_order_acl_exchange {M : Type w} [LinearOrder M] [DenselyOrdered M]
    [NoMinOrder M] [NoMaxOrder M] [Nonempty M] (A : Set M) (a b : M) :
    letI : binaryRelLanguage.Structure M := binaryRelStructure M (fun x y => x < y)
    b ∈ acl binaryRelLanguage (A ∪ {a}) \ acl binaryRelLanguage A →
      a ∈ acl binaryRelLanguage (A ∪ {b}) := by
  let : binaryRelLanguage.Structure M := binaryRelStructure M (fun x y => x < y)
  rw [(Lemmatheca.Entry.DefinableAndAlgebraicClosure.strictDlo_closures (A ∪ {a})).2,
    (Lemmatheca.Entry.DefinableAndAlgebraicClosure.strictDlo_closures A).2,
    (Lemmatheca.Entry.DefinableAndAlgebraicClosure.strictDlo_closures (A ∪ {b})).2]
  intro hb
  have he : b = a := hb.1.resolve_left hb.2
  exact Or.inr he.symm

abbrev pointLanguage := Language.empty[[Unit]]

def pointValue (M : Type w) [pointLanguage.Structure M] : M :=
  (Language.empty.con () : M)

def removePointConstant {α : Type*} (φ : pointLanguage.Formula α) :
    Language.empty.Formula (Unit ⊕ α) := BoundedFormula.constantsVarsEquiv φ

theorem removePointConstant_realize {M : Type w} [pointLanguage.Structure M]
    {α : Type*} (φ : pointLanguage.Formula α) (a : α → M) :
    letI : Language.empty.Structure M := (Language.empty.lhomWithConstants Unit).reduct M
    φ.Realize a ↔ (removePointConstant φ).Realize (Sum.elim (fun _ => pointValue M) a) := by
  let : Language.empty.Structure M := (Language.empty.lhomWithConstants Unit).reduct M
  exact (BoundedFormula.realize_constantsVarsEquiv (φ := φ) (v := a) (xs := Fin.elim0)).symm

private theorem point_definable_reduct {M : Type w} [pointLanguage.Structure M]
    {A s : Set M} (hs : A.Definable₁ pointLanguage s) :
    letI : Language.empty.Structure M := (Language.empty.lhomWithConstants Unit).reduct M
    (A ∪ {pointValue M}).Definable₁ Language.empty s := by
  let : Language.empty.Structure M := (Language.empty.lhomWithConstants Unit).reduct M
  obtain ⟨φ,hφ⟩ := Set.definable_iff_exists_formula_sum.mp hs
  let f : Unit ⊕ (A ⊕ Fin 1) → ↥(A ∪ {pointValue M}) ⊕ Fin 1 :=
    Sum.elim (fun _ => Sum.inl ⟨pointValue M,Or.inr rfl⟩)
      (Sum.elim (fun a => Sum.inl ⟨a.val,Or.inl a.property⟩) Sum.inr)
  apply Set.definable_iff_exists_formula_sum.mpr
  refine ⟨(removePointConstant φ).relabel f,?_⟩
  ext v
  rw [hφ]
  change φ.Realize (Sum.elim Subtype.val v) ↔ _
  rw [removePointConstant_realize]
  simp only [Formula.realize_relabel,Set.mem_ofPred_eq]
  apply iff_of_eq
  congr 1
  funext i
  rcases i with u | a | i <;> rfl

theorem point_stronglyMinimalTheory : StronglyMinimalTheory pointLanguage.infiniteTheory := by
  intro P
  let : Infinite P := pointLanguage.model_infiniteTheory_iff.mp P.is_model
  refine ⟨inferInstance,?_⟩
  intro s hs
  let : Language.empty.Structure P := (Language.empty.lhomWithConstants Unit).reduct P
  have h := point_definable_reduct hs
  exact (Lemmatheca.ModelTheory.QuantifierElimination.Shared.equality_definable_iff_finite_cofinite s).mp
    (h.mono (Set.subset_univ _))

theorem point_complete_theory {M : Type w} [pointLanguage.Structure M] [Infinite M] :
    StronglyMinimalTheory (pointLanguage.completeTheory M) ∧ StronglyMinimalStructure pointLanguage M := by
  have hs : StronglyMinimalTheory (pointLanguage.completeTheory M) := by
    intro N
    have hsub : pointLanguage.infiniteTheory ⊆ pointLanguage.completeTheory M := Theory.completeTheory.subset
    let : N ⊨ pointLanguage.infiniteTheory := N.is_model.mono hsub
    exact theory_model_minimal pointLanguage.infiniteTheory point_stronglyMinimalTheory
  exact ⟨hs,theory_model_stronglyMinimal (pointLanguage.completeTheory M) hs⟩

theorem point_closure {M : Type w} [pointLanguage.Structure M] [Infinite M] (A : Set M) :
    acl pointLanguage A = A ∪ {pointValue M} := by
  classical
  let : Language.empty.Structure M := (Language.empty.lhomWithConstants Unit).reduct M
  apply Set.Subset.antisymm
  · intro b hb
    obtain ⟨s,hs,hfin,hbs⟩ := hb
    have hd := point_definable_reduct hs
    have hbe : b ∈ acl Language.empty (A ∪ {pointValue M}) := ⟨s,hd,hfin,hbs⟩
    rwa [(Lemmatheca.Entry.DefinableAndAlgebraicClosure.infinite_equality_closures (A ∪ {pointValue M})).2] at hbe
  · intro b hb
    rcases hb with hb | hb
    · exact dcl_subset_acl A (subset_dcl A hb)
    · have he : b = pointValue M := hb
      subst b
      refine ⟨{pointValue M},?_,Set.finite_singleton _,Set.mem_singleton _⟩
      apply Set.definable_iff_exists_formula_sum.mpr
      refine ⟨(Term.var (Sum.inr (0 : Fin 1)) : pointLanguage.Term (A ⊕ Fin 1)).equal
        (Language.empty.con ()).term,?_⟩
      ext v
      simp only [Formula.realize_equal,Term.realize_var,Term.realize_constants,
        Set.mem_ofPred_eq,Set.mem_singleton_iff,Sum.elim_inr]
      rfl

theorem point_finite_basis {M : Type w} [pointLanguage.Structure M] [Infinite M] (S : Finset M) :
    letI := Classical.propDecidable
    let P := aclPregeometry pointLanguage.infiniteTheory point_stronglyMinimalTheory (M := M)
    P.IsBasis ((S.erase (pointValue M) : Finset M) : Set M) (acl pointLanguage (S : Set M)) ∧
      ∃ hS : P.FinitelyGenerated (acl pointLanguage (S : Set M)),
        P.finiteDimension (acl pointLanguage (S : Set M)) hS = (S.erase (pointValue M)).card := by
  classical
  let P := aclPregeometry pointLanguage.infiniteTheory point_stronglyMinimalTheory (M := M)
  have hcl (A : Set M) : P.cl A = A ∪ {pointValue M} := point_closure A
  have hb : P.IsBasis ((S.erase (pointValue M) : Finset M) : Set M) (acl pointLanguage (S : Set M)) := by
    refine ⟨?_,?_,?_⟩
    · exact fun x hx => dcl_subset_acl _ (subset_dcl _ (Finset.mem_of_mem_erase hx))
    · intro a ha hacl
      rw [hcl] at hacl
      rcases hacl with h | h
      · exact h.2 rfl
      · exact (Finset.mem_erase.mp ha).1 h
    · rw [hcl,point_closure]
      ext x
      simp only [Finset.mem_coe,Finset.mem_erase,Set.mem_union,Set.mem_singleton_iff]
      by_cases hx : x = pointValue M <;> simp_all
  have hg : P.FinitelyGenerated (acl pointLanguage (S : Set M)) := ⟨S,rfl⟩
  exact ⟨hb,hg,P.finiteDimension_eq_card _ hg _ hb⟩

theorem point_empty_dimension {M : Type w} [pointLanguage.Structure M] [Infinite M] :
    let P := aclPregeometry pointLanguage.infiniteTheory point_stronglyMinimalTheory (M := M)
    acl pointLanguage (∅ : Set M) = {pointValue M} ∧
      ∃ h : P.FinitelyGenerated {pointValue M}, P.finiteDimension {pointValue M} h = 0 := by
  classical
  let P := aclPregeometry pointLanguage.infiniteTheory point_stronglyMinimalTheory (M := M)
  have he : acl pointLanguage (∅ : Set M) = {pointValue M} := by simp only [point_closure,Set.empty_union]
  obtain ⟨_,hg,hd⟩ := point_finite_basis (M := M) (∅ : Finset M)
  have hg' : P.FinitelyGenerated {pointValue M} := by simpa only [Finset.coe_empty,he] using hg
  refine ⟨he,hg',?_⟩
  have hh : P.IsBasis ∅ {pointValue M} := by
    simpa only [Finset.erase_empty,Finset.coe_empty,he] using (point_finite_basis (M := M) (∅ : Finset M)).1
  simpa only [Finset.card_empty] using P.finiteDimension_eq_card _ hg' (∅ : Finset M) (by simpa only [Finset.coe_empty] using hh)

end
end Lemmatheca.Entry.StronglyMinimalSets
