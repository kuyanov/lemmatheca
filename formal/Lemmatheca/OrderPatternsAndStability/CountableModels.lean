import Lemmatheca.OrderPatternsAndStability.TypesAndCuts
import Lemmatheca.ElementarySubmodels.ElementarySubmodels

/-! The actual old parameter labels inside a countable elementary submodel. -/
namespace Lemmatheca.ModelTheory.OrderPatternsAndStability
open FirstOrder FirstOrder.Language Cardinal
universe u v w
variable {L : Language.{u,v}} {M : Type w} [L.Structure M]

/-- Keep each original A-label, interpreting it by the same point inside the submodel. -/
@[instance_reducible]
def submodelNamedStructure (S : L.ElementarySubstructure M) (A : Set M) (hA : A ⊆ S) :
    L[[A]].Structure S :=
  Diagrams.namedExpansion (L := L) (fun a : A => (⟨a.val,hA a.property⟩ : S))

private def namedSubtype (S : L.ElementarySubstructure M) (A : Set M) (hA : A ⊆ S) :
    @ElementaryEmbedding L[[A]] S M (submodelNamedStructure S A hA) inferInstance := by
  letI := submodelNamedStructure S A hA
  let : (L.lhomWithConstants A).IsExpansionOn S :=
    Diagrams.namedExpansion_isExpansion (L := L) (fun a : A => (⟨a.val,hA a.property⟩ : S))
  refine ⟨Subtype.val,?_⟩
  intro n φ a
  have hh := S.subtype.map_formula (BoundedFormula.constantsVarsEquiv φ)
    (Sum.elim (fun c : A => (⟨c.val,hA c.property⟩ : S)) a)
  have hm := BoundedFormula.realize_constantsVarsEquiv (M := M) (φ := φ)
    (v := Subtype.val ∘ a) (xs := Fin.elim0)
  have hs := BoundedFormula.realize_constantsVarsEquiv (M := S) (φ := φ)
    (v := a) (xs := Fin.elim0)
  have he : S.subtype ∘ Sum.elim (fun c : A => (⟨c.val,hA c.property⟩ : S)) a =
      Sum.elim (fun c : A => (c : M)) (Subtype.val ∘ a) := by
    funext i
    cases i <;> rfl
  rw [he] at hh
  exact hm.symm.trans (hh.trans hs)

private theorem type_formulas_injective {K : Language} (T : K.Theory) (r : ℕ) :
    Function.Injective (fun q : T.CompleteType (Fin r) => Types.formulas q) := by
  intro p q hp
  apply SetLike.ext'
  change p.toTheory = q.toTheory
  apply Set.ext
  intro γ
  have h := Set.ext_iff.mp hp (Formula.equivSentence.symm γ)
  change Formula.equivSentence (Formula.equivSentence.symm γ) ∈ p.toTheory ↔
    Formula.equivSentence (Formula.equivSentence.symm γ) ∈ q.toTheory at h
  simpa only [Equiv.apply_symm_apply] using h

private theorem countable_type_upper [Countable L.Symbols] {N : Type w} [L.Structure N]
    (A : Set N) (hA : A.Countable) :
    #(TypesOver (L := L) A 1) ≤ 2 ^ (ℵ₀ : Cardinal.{max u v w}) := by
  apply (parameter_type_count A 1).trans
  apply Cardinal.power_le_power_left (by simp)
  exact max_le (Cardinal.lift_le_aleph0.mpr Cardinal.mk_le_aleph0)
    (max_le le_rfl (Cardinal.lift_le_aleph0.mpr (Cardinal.mk_le_aleph0_iff.mpr hA.to_subtype)))

private theorem type_restriction_bound {N : Type w} [L.Structure N] [Nonempty N]
    {A B : Set N} (hAB : A ⊆ B) : #(TypesOver (L := L) A 1) ≤ #(TypesOver (L := L) B 1) := by
  classical
  let e (p : TypesOver (L := L) A 1) : TypesOver (L := L) B 1 :=
    (Types.restriction_surjective hAB p).choose
  have he (p : TypesOver (L := L) A 1) :
      Types.restrictFormulas hAB (Types.formulas (e p)) = Types.formulas p :=
    (Types.restriction_surjective hAB p).choose_spec
  apply Cardinal.mk_le_of_injective (f := e)
  intro p q hpq
  apply type_formulas_injective
  exact (he p).symm.trans ((congrArg (fun r => Types.restrictFormulas hAB (Types.formulas r)) hpq).trans (he q))

theorem submodel_named_theory (S : L.ElementarySubstructure M) [Nonempty M]
    (A : Set M) (hA : A ⊆ S) :
    letI := submodelNamedStructure S A hA
    L[[A]].completeTheory S = L[[A]].completeTheory M := by
  let := submodelNamedStructure S A hA
  exact (namedSubtype S A hA).elementarilyEquivalent

theorem complete_infinite_models (T : L.Theory) (hT : T.IsComplete)
    (hinf : ∃ P : Theory.ModelType.{u,v,max u v} T, Infinite P)
    [Nonempty M] [M ⊨ T] : Infinite M := by
  obtain ⟨P,hP⟩ := hinf
  have he : M ≅[L] P := by
    change L.completeTheory M = L.completeTheory P
    rw [← hT.eq_complete_theory M,← hT.eq_complete_theory P]
  exact he.infinite_iff.mpr hP

theorem countable_model_type_equalities [Countable L.Symbols] [Nonempty M]
    (T : L.Theory) (hT : T.IsComplete)
    (hinf : ∃ P : Theory.ModelType.{u,v,max u v} T, Infinite P) [M ⊨ T]
    {n : ℕ} (φ : L.Formula (Fin (1+n)))
    (a : ℚ → Fin 1 → M) (b : ℚ → Fin n → M) (h : OrderPattern φ a b) :
    ∃ S : L.ElementarySubstructure M,
      Countable S ∧ Infinite S ∧ ∃ hA : parameterSet b ⊆ S,
        letI := submodelNamedStructure S (parameterSet b) hA
        #( (L[[parameterSet b]].completeTheory S).CompleteType (Fin 1)) =
          2 ^ (ℵ₀ : Cardinal.{max u v w}) ∧
        #(TypesOver (L := L) (Set.univ : Set S) 1) =
          2 ^ (ℵ₀ : Cardinal.{max u v w}) := by
  classical
  let : Infinite M := complete_infinite_models T hT hinf
  let X := parameterSet a ∪ parameterSet b
  have hX : X.Countable := (parameterSet_countable a).union (parameterSet_countable b)
  obtain ⟨S,hXS,hS⟩ := L.exists_elementarySubstructure_card_eq X (ℵ₀ : Cardinal.{w}) le_rfl
    (by simpa only [Cardinal.lift_aleph0] using (Cardinal.lift_le_aleph0.mpr
      (Cardinal.mk_le_aleph0_iff.mpr hX.to_subtype)))
    (by simpa only [Cardinal.lift_aleph0,Language.card] using (Cardinal.lift_le_aleph0.mpr
      (Cardinal.mk_le_aleph0 (α := L.Symbols))))
    (by simpa only [Cardinal.lift_aleph0,Cardinal.lift_id] using
      (Cardinal.aleph0_le_mk M))
  have hc : #S = (ℵ₀ : Cardinal.{w}) := by simpa only [Cardinal.lift_id,Cardinal.lift_aleph0] using hS
  let : Countable S := Cardinal.mk_le_aleph0_iff.mp hc.le
  let : Infinite S := Cardinal.aleph0_le_mk_iff.mp hc.ge
  have hA : parameterSet b ⊆ S := fun _ hx => hXS (Or.inr hx)
  let a' (q : ℚ) (i : Fin 1) : S := ⟨a q i,hXS (Or.inl ⟨(q,i),rfl⟩)⟩
  let b' (q : ℚ) (i : Fin n) : S := ⟨b q i,hA ⟨(q,i),rfl⟩⟩
  have hp : OrderPattern φ a' b' := by
    intro i j
    have hs := S.subtype.map_formula φ (pairAssignment (a' i) (b' j))
    have he : S.subtype ∘ pairAssignment (a' i) (b' j) = pairAssignment (a i) (b j) := by
      funext k
      refine Fin.addCases ?_ ?_ k <;> intro k <;>
        simp only [Function.comp_apply,pairAssignment,Fin.addCases_left,Fin.addCases_right] <;> rfl
    rw [he] at hs
    exact hs.symm.trans (h i j)
  have hlower := rational_pattern_many_types φ a b h
  have hupper := countable_type_upper (L := L) (parameterSet b) (parameterSet_countable b)
  have hAllLower := (rational_pattern_many_types φ a' b' hp).trans
    (type_restriction_bound (L := L) (Set.subset_univ (parameterSet b')))
  have hAllUpper := countable_type_upper (L := L) (Set.univ : Set S) (Set.to_countable _)
  refine ⟨S,inferInstance,inferInstance,hA,?_⟩
  let := submodelNamedStructure S (parameterSet b) hA
  have ht := submodel_named_theory S (parameterSet b) hA
  constructor
  · rw [ht]
    exact le_antisymm hupper hlower
  · exact le_antisymm hAllUpper hAllLower

end Lemmatheca.ModelTheory.OrderPatternsAndStability
