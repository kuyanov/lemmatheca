import Lemmatheca.MembershipModels.MembershipModels
import Mathlib.ModelTheory.Satisfiability

namespace Lemmatheca.SetTheory.MembershipModels
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic.FirstOrderSyntax
open Lemmatheca.MathematicalLogic.FirstOrderSemantics
universe u
noncomputable section

abbrev chainLanguage := membershipLanguage[[ℕ]]

def chainSentence (n : ℕ) : chainLanguage.Sentence :=
  ((membershipLanguage.lhomWithConstants ℕ).onRelation BinaryRelationSymbol.rel).formula
    ![(membershipLanguage.con (n+1)).term, (membershipLanguage.con n).term]

def chainTheory (T : membershipLanguage.Theory) : chainLanguage.Theory :=
  (membershipLanguage.lhomWithConstants ℕ).onTheory T ∪ Set.range chainSentence

def reverseNumerals {M : Type u} (num : ℕ → M) (r : ℕ) : ℕ → M :=
  fun i => num (r-i)

@[instance_reducible] def chainExpansion {M : Type u} (E : M → M → Prop)
    (num : ℕ → M) (r : ℕ) : chainLanguage.Structure M :=
  @Language.withConstantsStructure membershipLanguage M (binaryRelStructure M E)
    ℕ (constantsOn.structure (reverseNumerals num r))

theorem reverseNumerals_link {M : Type u} {E : M → M → Prop}
    (num : ℕ → M) (hnum : ∀ n, E (num n) (num (n+1))) {r n : ℕ} (hn : n < r) :
    E (reverseNumerals num r (n+1)) (reverseNumerals num r n) := by
  unfold reverseNumerals
  have hh : r - n = (r - (n+1)) + 1 := by omega
  rw [hh]
  exact hnum _

theorem chainExpansion_link {M : Type u} {E : M → M → Prop}
    (num : ℕ → M) (hnum : ∀ n, E (num n) (num (n+1))) {r n : ℕ} (hn : n < r) :
    letI := chainExpansion E num r
    M ⊨ chainSentence n := by
  exact reverseNumerals_link num hnum hn

theorem chainTheory_finitely_satisfiable (T : membershipLanguage.Theory)
    {M : Type u} [Nonempty M] (E : M → M → Prop)
    (hT : letI := binaryRelStructure M E; M ⊨ T)
    (num : ℕ → M) (hnum : ∀ n, E (num n) (num (n+1))) :
    (chainTheory T).IsFinitelySatisfiable := by
  classical
  intro Γ hΓ
  let r (A : Γ) : ℕ :=
    if hA : (A : chainLanguage.Sentence) ∈ Set.range chainSentence then Classical.choose hA else 0
  let N := Finset.univ.sup r + 1
  let := binaryRelStructure M E
  let := constantsOn.structure (reverseNumerals num N)
  let := chainExpansion E num N
  have ht : M ⊨ (membershipLanguage.lhomWithConstants ℕ).onTheory T :=
    (LHom.onTheory_model _ _).mpr hT
  let : M ⊨ (↑Γ : chainLanguage.Theory) := by
    refine ⟨fun A hA => ?_⟩
    rcases hΓ hA with hOld | hNew
    · exact ht.realize_of_mem A hOld
    · have hr : chainSentence (r ⟨A,hA⟩) = A := by
        simpa only [r, dite_eq_left hNew] using Classical.choose_spec hNew
      rw [← hr]
      have hn : r ⟨A,hA⟩ < N := Nat.lt_succ_of_le (Finset.le_sup (f := r) (Finset.mem_univ _))
      exact chainExpansion_link num hnum hn
  exact Theory.Model.isSatisfiable M

theorem chainTheory_satisfiable (T : membershipLanguage.Theory)
    {M : Type u} [Nonempty M] (E : M → M → Prop)
    (hT : letI := binaryRelStructure M E; M ⊨ T)
    (num : ℕ → M) (hnum : ∀ n, E (num n) (num (n+1))) :
    (chainTheory T).IsSatisfiable := by
  exact Theory.isSatisfiable_iff_isFinitelySatisfiable.mpr
    (chainTheory_finitely_satisfiable T E hT num hnum)

/-- Forget exactly the added constants in the supplied compactness model. -/
def chainReduct (T : membershipLanguage.Theory) (B : Theory.ModelType (chainTheory T)) :
    Theory.ModelType T :=
  Theory.ModelType.reduct (membershipLanguage.lhomWithConstants ℕ)
    (B.subtheoryModel Set.subset_union_left)

/-- The descending sequence is exactly the interpretation of the added constants. -/
def chainConstants (T : membershipLanguage.Theory) (B : Theory.ModelType (chainTheory T)) :
    ℕ → chainReduct T B := fun n => (membershipLanguage.con n : B)

theorem chainReduct_specified_descent (T : membershipLanguage.Theory)
    (B : Theory.ModelType (chainTheory T)) :
    (chainReduct T B ⊨ T) ∧
    (∀ n, Structure.RelMap (L := membershipLanguage) BinaryRelationSymbol.rel
      ![chainConstants T B (n+1), chainConstants T B n]) ∧
    ¬ WellFounded (fun x y : chainReduct T B =>
      Structure.RelMap (L := membershipLanguage) BinaryRelationSymbol.rel ![x,y]) := by
  have hb (n : ℕ) : Structure.RelMap (L := membershipLanguage) BinaryRelationSymbol.rel
      ![chainConstants T B (n+1), chainConstants T B n] := by
    have h := B.is_model.realize_of_mem (chainSentence n) (Or.inr ⟨n,rfl⟩)
    have hh := (Formula.realize_rel (R :=
      (membershipLanguage.lhomWithConstants ℕ).onRelation BinaryRelationSymbol.rel)
      (ts := ![(membershipLanguage.con (n+1)).term, (membershipLanguage.con n).term])).mp h
    change @Structure.RelMap chainLanguage B B.struc 2
      ((membershipLanguage.lhomWithConstants ℕ).onRelation BinaryRelationSymbol.rel)
      ![(membershipLanguage.con (n+1) : B), (membershipLanguage.con n : B)]
    convert hh using 1
    funext i
    fin_cases i <;> simp
  refine ⟨inferInstance, hb, ?_⟩
  intro hw
  obtain ⟨a,⟨n,rfl⟩,hmin⟩ := hw.has_min (Set.range (chainConstants T B)) ⟨_,⟨0,rfl⟩⟩
  exact hmin (chainConstants T B (n+1)) ⟨n+1,rfl⟩ (hb n)

/-- The generic construction verifies the actual new theory and its constants.
The separate ZFC application remains unbound until ZFC's schemas are encoded. -/
theorem model_with_external_descent (T : membershipLanguage.Theory)
    {M : Type u} [Nonempty M] (E : M → M → Prop)
    (hT : letI := binaryRelStructure M E; M ⊨ T)
    (num : ℕ → M) (hnum : ∀ n, E (num n) (num (n+1))) :
    ∃ N : Theory.ModelType T, ∃ b : ℕ → N,
      (∀ n, Structure.RelMap (L := membershipLanguage) BinaryRelationSymbol.rel ![b (n+1), b n]) ∧
      ¬ WellFounded (fun x y : N =>
        Structure.RelMap (L := membershipLanguage) BinaryRelationSymbol.rel ![x,y]) := by
  obtain ⟨B⟩ := chainTheory_satisfiable T E hT num hnum
  exact ⟨chainReduct T B.ulift, chainConstants T B.ulift,
    (chainReduct_specified_descent T B.ulift).2⟩

end
end Lemmatheca.SetTheory.MembershipModels
