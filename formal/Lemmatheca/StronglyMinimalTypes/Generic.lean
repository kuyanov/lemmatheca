import Lemmatheca.StronglyMinimalSets.Minimality
import Lemmatheca.TypesAndRealization.Types
import Lemmatheca.IsolatedTypes.IsolatedTypes
import Lemmatheca.OrderPatternsAndStability.TypesAndCuts

/-! Cofinite generic one-types in the actual named-parameter syntax.
The closure below is the shared definable-set algebraic closure, not a replacement.
-/
namespace Lemmatheca.ModelTheory.StronglyMinimalTypes
open FirstOrder FirstOrder.Language
open Lemmatheca.ModelTheory
open StronglyMinimalSets Closures OrderPatternsAndStability
universe u v w w' z
noncomputable section
variable {L : Language.{u,v}} {M : Type w} [L.Structure M] [nonemptyM : Nonempty M]

/-- Unary solutions in the original, canonically named parameter expansion. -/
def solutions (A : Set M) (φ : L[[A]].Formula (Fin 1)) : Set M :=
  {b | φ.Realize (fun _ => b)}

/-- The same formula in the extension, interpreting each old name by the specified map. -/
def extensionSolutions {N : Type w'} [L.Structure N] (f : M ↪ₑ[L] N)
    (A : Set M) (φ : L[[A]].Formula (Fin 1)) : Set N :=
  {b | @Formula.Realize _ (f.toEmbedding.withConstants A) _ _ φ (fun _ => b)}

/-- A complete type is algebraic when it contains one finite-solution formula. -/
def Algebraic (A : Set M) (q : TypesOver (L := L) A 1) : Prop :=
  ∃ φ ∈ Types.formulas q, (solutions A φ).Finite

/-- Nonalgebraic means that no formula in the complete type has finitely many solutions. -/
def Nonalgebraic (A : Set M) (q : TypesOver (L := L) A 1) : Prop := ¬ Algebraic A q

/-- All actual named-parameter formulas whose old solution sets are cofinite. -/
def cofiniteConditions (A : Set M) : Set (L[[A]].Formula (Fin 1)) :=
  {φ | Cofinite (solutions A φ)}

/-- Every unary definable set is the solution set of one actual parameter formula. -/
theorem definable_iff_solutions (A : Set M) (s : Set M) :
    A.Definable₁ L s ↔ ∃ φ : L[[A]].Formula (Fin 1), s = solutions A φ := by
  rcases nonemptyM with ⟨_sourcePoint⟩
  constructor
  · rintro ⟨φ, hφ⟩
    refine ⟨φ, Set.ext fun b => ?_⟩
    exact Set.ext_iff.mp hφ (fun _ => b)
  · rintro ⟨φ, rfl⟩
    refine ⟨φ, Set.ext fun a => ?_⟩
    change φ.Realize (fun _ => a 0) ↔ φ.Realize a
    have he : (fun _ : Fin 1 => a 0) = a := by
      funext i
      rw [Subsingleton.elim i 0]
    rw [he]

/-- This bridge identifies the formula presentation with the shared algebraic closure. -/
theorem mem_acl_iff_formula (A : Set M) (b : M) :
    b ∈ acl L A ↔ ∃ φ : L[[A]].Formula (Fin 1),
      (solutions A φ).Finite ∧ b ∈ solutions A φ := by
  constructor
  · rintro ⟨s, hs, hf, hb⟩
    obtain ⟨φ, rfl⟩ := (definable_iff_solutions A s).mp hs
    exact ⟨φ, hf, hb⟩
  · rintro ⟨φ, hf, hb⟩
    exact ⟨solutions A φ, (definable_iff_solutions A _).mpr ⟨φ, rfl⟩, hf, hb⟩

/-- Finite fibers are preserved exactly by the specified elementary embedding. -/
theorem finite_solutions_image {N : Type w'} [L.Structure N] (f : M ↪ₑ[L] N)
    (A : Set M) (φ : L[[A]].Formula (Fin 1)) (hφ : (solutions A φ).Finite) :
    extensionSolutions f A φ = f '' solutions A φ := by
  rcases nonemptyM with ⟨_sourcePoint⟩
  let ψ := Types.parameterFormula A φ
  have hm : {x : M | ψ.Realize (Sum.elim id (fun _ => x))} = solutions A φ := by
    ext x
    exact Types.parameterFormula_realize (ElementaryEmbedding.refl L M) A φ (fun _ => x)
  have hn : {y : N | ψ.Realize (Sum.elim (f ∘ id) (fun _ => y))} =
      extensionSolutions f A φ := by
    ext y
    change ψ.Realize (Sum.elim (f ∘ id) (fun _ => y)) ↔
      @Formula.Realize _ (f.toEmbedding.withConstants A) _ _ φ (fun _ => y)
    exact Types.parameterFormula_realize f A φ (fun _ => y)
  have he := Closures.elementary_finite_fiber f ψ id (hm.symm ▸ hφ)
  rwa [hm, hn] at he

omit [Nonempty M] in
private theorem solutions_not (A : Set M) (φ : L[[A]].Formula (Fin 1)) :
    solutions A φ.not = (solutions A φ)ᶜ := by
  ext b
  exact Formula.realize_not

omit [Nonempty M] in
private theorem extensionSolutions_not {N : Type w'} [L.Structure N] (f : M ↪ₑ[L] N)
    (A : Set M) (φ : L[[A]].Formula (Fin 1)) :
    extensionSolutions f A φ.not = (extensionSolutions f A φ)ᶜ := by
  ext b
  change @Formula.Realize _ (f.toEmbedding.withConstants A) _ _ φ.not (fun _ => b) ↔
    ¬ @Formula.Realize _ (f.toEmbedding.withConstants A) _ _ φ (fun _ => b)
  exact Formula.realize_not

/-- The finite complement of a cofinite formula is the same image of old excluded points. -/
theorem cofinite_complement_image {N : Type w'} [L.Structure N] (f : M ↪ₑ[L] N)
    (A : Set M) (φ : L[[A]].Formula (Fin 1)) (hφ : Cofinite (solutions A φ)) :
    (extensionSolutions f A φ)ᶜ = f '' (solutions A φ)ᶜ := by
  have hf : (solutions A φ.not).Finite := (solutions_not A φ).symm ▸ hφ
  have h := finite_solutions_image f A φ.not hf
  rwa [solutions_not, extensionSolutions_not] at h

/-- Minimality applies to every formula in the parameter expansion. -/
theorem parameter_dichotomy (A : Set M) (hM : Minimal L M)
    (φ : L[[A]].Formula (Fin 1)) :
    (solutions A φ).Finite ∨ Cofinite (solutions A φ) := by
  exact hM.2 _ (((definable_iff_solutions A _).mpr ⟨φ, rfl⟩).mono (Set.subset_univ A))

/-- Avoiding a finite union of complements gives a common old witness. -/
theorem cofinite_finitely_realized (A : Set M) (hM : Minimal L M) :
    Types.FinitelyRealized M (cofiniteConditions (L := L) A) := by
  rcases nonemptyM with ⟨_sourcePoint⟩
  classical
  let : Infinite M := hM.1
  intro s hs
  let bad : Set M := ⋃ φ : s, (solutions A φ.val)ᶜ
  have hbad : bad.Finite := Set.finite_iUnion fun φ => hs φ.property
  obtain ⟨b, hb⟩ := hbad.exists_notMem
  refine ⟨fun _ => b, fun φ hφ => ?_⟩
  by_contra hnot
  apply hb
  exact Set.mem_iUnion.mpr ⟨⟨φ, hφ⟩, hnot⟩

/-- The cofinite collection is complete in the shared maximal-formula presentation. -/
theorem cofinite_complete (A : Set M) (hM : Minimal L M) :
    Types.IsCompletePartial (L[[A]].completeTheory M) (cofiniteConditions A) := by
  apply (Types.complete_iff_decides _ _).mpr
  refine ⟨(Types.partial_iff_finitelyRealized_completeTheory _).mpr
    (cofinite_finitely_realized A hM), fun φ => ?_⟩
  rcases parameter_dichotomy A hM φ with hf | hc
  · right
    change (solutions A φ.not)ᶜ.Finite
    rw [solutions_not, compl_compl]
    exact hf
  · exact Or.inl hc

/-- Choose the actual mathlib complete type corresponding to the complete cofinite formulas. -/
def genericType (A : Set M) (hM : Minimal L M) : TypesOver (L := L) A 1 :=
  ((Types.complete_iff_mathlib _ _).mp (cofinite_complete A hM)).choose

/-- Exact formula-set identity prevents a separate local notion of generic type. -/
theorem genericType_formulas (A : Set M) (hM : Minimal L M) :
    Types.formulas (genericType A hM) = cofiniteConditions A := by
  exact (((Types.complete_iff_mathlib _ _).mp (cofinite_complete A hM)).choose_spec).1

/-- Every generic formula has infinite solution set. -/
theorem generic_nonalgebraic (A : Set M) (hM : Minimal L M) :
    Nonalgebraic A (genericType A hM) := by
  let : Infinite M := hM.1
  rintro ⟨φ, hφ, hf⟩
  rw [genericType_formulas] at hφ
  have hu : (Set.univ : Set M).Finite := by
    simpa only [Set.union_compl_self] using hf.union hφ
  exact Set.infinite_univ hu

/-- Every other complete one-type contains a finite-solution formula. -/
theorem unique_nonalgebraic (A : Set M) (hM : Minimal L M)
    (q : TypesOver (L := L) A 1) (hq : Nonalgebraic A q) :
    q = genericType A hM := by
  obtain ⟨N, a, ha⟩ := (Types.partial_iff_model _ _).mp (Types.partial_formulas q)
  have hg : Types.Realizes (Types.formulas (genericType A hM)) a := by
    intro φ hφ
    rcases q.mem_or_not_mem (Formula.equivSentence φ) with hqφ | hqn
    · exact ha φ hqφ
    · exfalso
      apply hq
      refine ⟨φ.not, ?_, ?_⟩
      · change Formula.equivSentence φ.not ∈ q.toTheory
        rw [Formula.equivSentence_not]
        exact hqn
      · rw [genericType_formulas] at hφ
        exact (solutions_not A φ).symm ▸ hφ
  exact ((Types.realizes_complete_iff q a).mp ha).trans
    ((Types.realizes_complete_iff (genericType A hM) a).mp hg).symm

/-- The named extension type uses the original named theory and the specific elementary map. -/
def extensionType {N : Type w'} [L.Structure N] [Nonempty N]
    (f : M ↪ₑ[L] N) (A : Set M) (b : N) : TypesOver (L := L) A 1 := by
  letI : L[[A]].Structure N := inferInstanceAs (L[[A]].Structure (f.toEmbedding.withConstants A))
  letI : N ⊨ L[[A]].completeTheory M :=
    ((f.liftWithConstants A).theory_model_iff _).mp (inferInstance : M ⊨ L[[A]].completeTheory M)
  exact (L[[A]].completeTheory M).typeOf (fun _ => b)

/-- Membership in the old-parameter type is truth with exactly those names interpreted by f. -/
theorem extensionType_membership {N : Type w'} [L.Structure N] [Nonempty N]
    (f : M ↪ₑ[L] N) (A : Set M) (b : N) (φ : L[[A]].Formula (Fin 1)) :
    φ ∈ Types.formulas (extensionType f A b) ↔ b ∈ extensionSolutions f A φ := by
  rcases nonemptyM with ⟨_sourcePoint⟩
  exact @Theory.CompleteType.formula_mem_typeOf _ _ _ (f.toEmbedding.withConstants A)
    inferInstance (inferInstance : Nonempty N)
    (((f.liftWithConstants A).theory_model_iff _).mp
      (inferInstance : M ⊨ L[[A]].completeTheory M)) _ _


private theorem formulas_injective {K : Language} {T : K.Theory} :
    Function.Injective (fun q : T.CompleteType (Fin 1) => Types.formulas q) := by
  intro p q hpq
  apply SetLike.ext
  intro γ
  change γ ∈ p.toTheory ↔ γ ∈ q.toTheory
  have h := Set.ext_iff.mp hpq (Formula.equivSentence.symm γ)
  simpa only [Types.formulas, Set.mem_preimage, Equiv.apply_symm_apply] using h


private theorem extensionType_eq_of_realizes {N : Type w'} [L.Structure N] [Nonempty N]
    (f : M ↪ₑ[L] N) (A : Set M) (q : TypesOver (L := L) A 1) (b : N)
    (hb : @Types.Realizes _ _ (f.toEmbedding.withConstants A) _
      (Types.formulas q) (fun _ => b)) : q = extensionType f A b := by
  apply formulas_injective
  ext φ
  constructor
  · intro hφ
    exact (extensionType_membership f A b φ).mpr (hb φ hφ)
  · intro hφ
    rcases q.mem_or_not_mem (Formula.equivSentence φ) with ht | hn
    · exact ht
    · have hn' : φ.not ∈ Types.formulas q := by
        change Formula.equivSentence φ.not ∈ q.toTheory
        rw [Formula.equivSentence_not]
        exact hn
      exact False.elim ((Formula.realize_not.mp (hb φ.not hn'))
        ((extensionType_membership f A b φ).mp hφ))

/-- The type of a mapped old point is exactly its original parameter type. -/
theorem extensionType_old_point {N : Type w'} [L.Structure N] [Nonempty N]
    (f : M ↪ₑ[L] N) (A : Set M) (b : M) :
    extensionType f A (f b) = (L[[A]].completeTheory M).typeOf (fun _ => b) := by
  apply formulas_injective
  ext φ
  rw [extensionType_membership]
  exact (Types.parameter_type_transport f A (fun _ => b) φ).symm.trans
    Theory.CompleteType.formula_mem_typeOf.symm

/-- Generic realizations are precisely the points outside shared algebraic closure. -/
theorem generic_realization {N : Type w'} [L.Structure N] [Nonempty N]
    (f : M ↪ₑ[L] N) (A : Set M) (hM : Minimal L M) (b : N) :
    extensionType f A b = genericType A hM ↔ b ∉ acl L (f '' A) := by
  constructor
  · intro he hb
    rw [← Closures.elementary_image_acl f A] at hb
    obtain ⟨a, ha, rfl⟩ := hb
    obtain ⟨φ, hf, hφa⟩ := (mem_acl_iff_formula A a).mp ha
    have hφ : φ ∈ Types.formulas (extensionType f A (f a)) :=
      (extensionType_membership f A (f a) φ).mpr
        ((Types.parameter_type_transport f A (fun _ => a) φ).mp hφa)
    exact generic_nonalgebraic A hM ⟨φ, he ▸ hφ, hf⟩
  · intro hb
    apply unique_nonalgebraic A hM
    rintro ⟨φ, hφ, hf⟩
    have hm := (extensionType_membership f A b φ).mp hφ
    rw [finite_solutions_image f A φ hf] at hm
    obtain ⟨a, ha, rfl⟩ := hm
    apply hb
    rw [← Closures.elementary_image_acl f A]
    exact ⟨a, (mem_acl_iff_formula A a).mpr ⟨φ, hf, ha⟩, rfl⟩

/-- The generic type is consistent and realized somewhere with every old parameter retained. -/
theorem generic_elementary_realization (A : Set M) (hM : Minimal L M) :
    ∃ (N : Type (max u v w)) (_ : L.Structure N) (_ : Nonempty N),
      ∃ (f : M ↪ₑ[L] N) (b : N),
        @Types.Realizes _ _ (f.toEmbedding.withConstants A) _
          (Types.formulas (genericType A hM)) (fun _ => b) := by
  have hf : Types.FinitelyRealized M (Types.formulas (genericType A hM)) := by
    rw [genericType_formulas]
    exact cofinite_finitely_realized A hM
  obtain ⟨N, SN, hN, f, b, hb⟩ := (Types.parameter_realization A _).mp hf
  let := SN
  let := hN
  refine ⟨N, SN, hN, f, b 0, ?_⟩
  have he : (fun _ : Fin 1 => b 0) = b := by
    funext i
    rw [Subsingleton.elim i 0]
  rwa [he]

/-- Already in the original structure the generic points are the complement of acl. -/
theorem generic_old_realization (A : Set M) (hM : Minimal L M) (b : M) :
    (L[[A]].completeTheory M).typeOf (fun _ => b) = genericType A hM ↔
      b ∉ acl L A := by
  have h := generic_realization (ElementaryEmbedding.refl L M) A hM b
  have he := extensionType_old_point (ElementaryEmbedding.refl L M) A b
  change extensionType (ElementaryEmbedding.refl L M) A b = _ at he
  rw [he] at h
  change _ ↔ b ∉ acl L (id '' A) at h
  simpa only [Set.image_id] using h

/-- The original tuple type is algebraic precisely when its point is algebraic over A. -/
theorem algebraic_typeOf_iff (A : Set M) (b : M) :
    Algebraic A ((L[[A]].completeTheory M).typeOf (fun _ => b)) ↔ b ∈ acl L A := by
  rw [mem_acl_iff_formula]
  constructor
  · rintro ⟨φ, hφ, hf⟩
    exact ⟨φ, hf, Theory.CompleteType.formula_mem_typeOf.mp hφ⟩
  · rintro ⟨φ, hf, hφ⟩
    exact ⟨φ, Theory.CompleteType.formula_mem_typeOf.mpr hφ, hf⟩

/-- Every algebraic parameter type is realized by an algebraic point in the source. -/
theorem algebraic_realized (A : Set M) (q : TypesOver (L := L) A 1)
    (hq : Algebraic A q) :
    ∃ b : M, b ∈ acl L A ∧ q = (L[[A]].completeTheory M).typeOf (fun _ => b) := by
  obtain ⟨φ, hφ, hf⟩ := hq
  have hfr := (Types.partial_iff_finitelyRealized_completeTheory (Types.formulas q)).mp
    (Types.partial_formulas q)
  obtain ⟨N, SN, hN, f, b, hb⟩ := (Types.parameter_realization A _).mp hfr
  let := SN
  let := hN
  have he : (fun _ : Fin 1 => b 0) = b := by
    funext i
    rw [Subsingleton.elim i 0]
  have hr : @Types.Realizes _ _ (f.toEmbedding.withConstants A) _
      (Types.formulas q) (fun _ => b 0) := he.symm ▸ hb
  have hmem : b 0 ∈ extensionSolutions f A φ := hr φ hφ
  rw [finite_solutions_image f A φ hf] at hmem
  obtain ⟨a, ha, hea⟩ := hmem
  refine ⟨a, (mem_acl_iff_formula A a).mpr ⟨φ, hf, ha⟩, ?_⟩
  have hqext := extensionType_eq_of_realizes f A q (b 0) hr
  rw [← hea, extensionType_old_point] at hqext
  exact hqext

/-- The specified map used to count the algebraic types. -/
def algebraicPointType (A : Set M) : acl L A → {q : TypesOver (L := L) A 1 // Algebraic A q} :=
  fun b => ⟨(L[[A]].completeTheory M).typeOf (fun _ => b.val),
    (algebraic_typeOf_iff A b.val).mpr b.property⟩

/-- Every algebraic type is hit by the exact point-to-type map. -/
theorem algebraicPointType_surjective (A : Set M) :
    Function.Surjective (algebraicPointType (L := L) A) := by
  rintro ⟨q, hq⟩
  obtain ⟨b, hb, htype⟩ := algebraic_realized A q hq
  refine ⟨⟨b, hb⟩, Subtype.ext ?_⟩
  exact htype.symm

/-- Only finitely many complete types can contain one finite-solution formula. -/
theorem finite_types_over_finite_formula (A : Set M) (φ : L[[A]].Formula (Fin 1))
    (hφ : (solutions A φ).Finite) :
    {q : TypesOver (L := L) A 1 | φ ∈ Types.formulas q}.Finite := by
  let f : M → TypesOver (L := L) A 1 := fun b => (L[[A]].completeTheory M).typeOf (fun _ => b)
  apply (hφ.image f).subset
  intro q hq
  obtain ⟨b, hb, he⟩ := algebraic_realized A q ⟨φ, hq, hφ⟩
  refine ⟨b, ?_, he.symm⟩
  have hqb : φ ∈ Types.formulas ((L[[A]].completeTheory M).typeOf (fun _ => b)) := he ▸ hq
  exact Theory.CompleteType.formula_mem_typeOf.mp hqb

/-- The finite distinguishing conjunction displayed in the isolation argument. -/
def refinement {I : Type z} [Fintype I] (A : Set M)
    (φ : L[[A]].Formula (Fin 1)) (ψ : I → L[[A]].Formula (Fin 1)) :
    L[[A]].Formula (Fin 1) := φ ⊓ Formula.iInf ψ

/-- The specified conjunction isolates the retained type when its factors exclude all others. -/
theorem refinement_isolates {I : Type z} [Fintype I] (A : Set M)
    (q : TypesOver (L := L) A 1) (φ : L[[A]].Formula (Fin 1))
    (hφ : φ ∈ Types.formulas q) (hfin : (solutions A φ).Finite)
    (others : I → TypesOver (L := L) A 1)
    (hcover : ∀ r : TypesOver (L := L) A 1, φ ∈ Types.formulas r →
      r = q ∨ ∃ i, others i = r)
    (ψ : I → L[[A]].Formula (Fin 1))
    (hψ : ∀ i, ψ i ∈ Types.formulas q ∧ ψ i ∉ Types.formulas (others i)) :
    (solutions A (refinement A φ ψ)).Finite ∧
      IsolatedTypes.Isolates (L[[A]].completeTheory M) q (refinement A φ ψ) := by
  rcases nonemptyM with ⟨_sourcePoint⟩
  classical
  refine ⟨hfin.subset (fun b hb => (Formula.realize_inf.mp hb).1), ?_⟩
  apply (IsolatedTypes.isolates_iff_unique q _).mpr
  obtain ⟨N, a, ha⟩ := (Types.partial_iff_model _ _).mp (Types.partial_formulas q)
  have heq := (Types.realizes_complete_iff q a).mp ha
  have hθa : (refinement A φ ψ).Realize a :=
    Formula.realize_inf.mpr ⟨ha φ hφ, Formula.realize_iInf.mpr (fun i => ha _ (hψ i).1)⟩
  have hθq : refinement A φ ψ ∈ Types.formulas q := by
    rw [heq]
    exact Theory.CompleteType.formula_mem_typeOf.mpr hθa
  refine ⟨hθq, fun r hr => ?_⟩
  obtain ⟨P, b, hb⟩ := (Types.partial_iff_model _ _).mp (Types.partial_formulas r)
  have hθb := Formula.realize_inf.mp (hb _ hr)
  have hrφ : φ ∈ Types.formulas r := by
    rw [(Types.realizes_complete_iff r b).mp hb]
    exact Theory.CompleteType.formula_mem_typeOf.mpr hθb.1
  rcases hcover r hrφ with he | ⟨i, hi⟩
  · exact he
  · exfalso
    apply (hψ i).2
    rw [hi, (Types.realizes_complete_iff r b).mp hb]
    exact Theory.CompleteType.formula_mem_typeOf.mpr ((Formula.realize_iInf.mp hθb.2) i)

/-- A finite formula has a finite refinement isolating any of its compatible complete types. -/
theorem algebraic_isolated (A : Set M) (q : TypesOver (L := L) A 1)
    (hq : Algebraic A q) :
    ∃ θ : L[[A]].Formula (Fin 1), (solutions A θ).Finite ∧
      IsolatedTypes.Isolates (L[[A]].completeTheory M) q θ := by
  classical
  obtain ⟨φ, hφ, hfin⟩ := hq
  let others : Set (TypesOver (L := L) A 1) := {r | φ ∈ Types.formulas r ∧ r ≠ q}
  have hothers : others.Finite := (finite_types_over_finite_formula A φ hfin).subset
    (fun _ h => h.1)
  let : Fintype others := hothers.fintype
  have hsep : ∀ r : others, ∃ ψ : L[[A]].Formula (Fin 1),
      ψ ∈ Types.formulas q ∧ ψ ∉ Types.formulas r.val := by
    intro r
    obtain ⟨ψ, hp, hn⟩ := IsolatedTypes.separates q r.val r.property.2.symm
    refine ⟨ψ, hp, ?_⟩
    change Formula.equivSentence ψ.not ∈ r.val.toTheory at hn
    rw [Formula.equivSentence_not] at hn
    exact (r.val.not_mem_iff _).mp hn
  choose ψ hψ using hsep
  refine ⟨refinement A φ ψ, ?_⟩
  apply refinement_isolates A q φ hφ hfin Subtype.val ?_ ψ hψ
  intro r hr
  by_cases h : r = q
  · exact Or.inl h
  · exact Or.inr ⟨⟨r, hr, h⟩, rfl⟩

end
end Lemmatheca.ModelTheory.StronglyMinimalTypes
