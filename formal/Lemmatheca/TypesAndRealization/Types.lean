import Mathlib.ModelTheory.Types
import Lemmatheca.DiagramsAndExtensions.Diagrams

/-! Partial and complete types in the shared first-order syntax.
The formula-to-named-sentence equivalence connects the human presentation to
mathlib's complete types; parameter realization retains the specified elementary map.
-/

namespace Lemmatheca.ModelTheory.Types

open FirstOrder FirstOrder.Language

universe u v w w' z

variable {L : Language.{u, v}} {T : L.Theory} {α : Type w}

/-- All the conditions of a type hold at this specified tuple. -/
def Realizes {M : Type w'} [L.Structure M] (p : Set (L.Formula α)) (a : α → M) : Prop :=
  ∀ φ ∈ p, φ.Realize a

/-- No tuple in the specified structure realizes all the conditions. -/
def Omits (M : Type w') [L.Structure M] (p : Set (L.Formula α)) : Prop :=
  ¬ ∃ a : α → M, Realizes p a

/-- Name the free tuple, retaining the whole background theory. -/
def namedTheory (T : L.Theory) (p : Set (L.Formula α)) : L[[α]].Theory :=
  (L.lhomWithConstants α).onTheory T ∪ Formula.equivSentence '' p

/-- Semantic consistency of all the displayed conditions with the background theory. -/
def IsPartial (T : L.Theory) (p : Set (L.Formula α)) : Prop :=
  (namedTheory T p).IsSatisfiable

/-- Maximality is among consistent formula collections in the same free context. -/
def IsCompletePartial (T : L.Theory) (p : Set (L.Formula α)) : Prop :=
  IsPartial T p ∧ ∀ q, IsPartial T q → p ⊆ q → q = p

/-- Pull back the named sentences of an actual mathlib complete type to formulas. -/
def formulas (q : T.CompleteType α) : Set (L.Formula α) :=
  Formula.equivSentence ⁻¹' q.toTheory

/-- Every finite subcollection has a common realizing tuple in this fixed structure. -/
def FinitelyRealized (M : Type w') [L.Structure M] (p : Set (L.Formula α)) : Prop :=
  ∀ s : Finset (L.Formula α), (↑s : Set _) ⊆ p → ∃ a : α → M, Realizes (↑s : Set (L.Formula α)) a

private theorem partial_of_realizes {M : Type w'} [L.Structure M] [Nonempty M] [M ⊨ T]
    (p : Set (L.Formula α)) (a : α → M) (ha : Realizes p a) : IsPartial T p := by
  let : L[[α]].Structure M := Diagrams.namedExpansion a
  let : (L.lhomWithConstants α).IsExpansionOn M := Diagrams.namedExpansion_isExpansion a
  have : M ⊨ namedTheory T p := by
    constructor
    intro γ hγ
    rcases hγ with hT | ⟨φ, hφ, rfl⟩
    · obtain ⟨σ, hσ, rfl⟩ := hT
      exact (LHom.realize_onSentence M _ _).mpr (Theory.realize_sentence_of_mem T hσ)
    · exact (Formula.realize_equivSentence M φ).mpr (ha φ hφ)
  exact Theory.Model.isSatisfiable M

/-- The consistency definition is precisely realization in a nonempty model of the theory. -/
theorem partial_iff_model (T : L.Theory) (p : Set (L.Formula α)) :
    IsPartial T p ↔ ∃ N : Theory.ModelType.{u, v, max u v w} T,
      ∃ a : α → N, Realizes p a := by
  constructor
  · intro hp
    let B := hp.some
    let : L.Structure B := (L.lhomWithConstants α).reduct B
    let : (L.lhomWithConstants α).IsExpansionOn B := LHom.isExpansionOn_reduct _ _
    have hT : B ⊨ T := (LHom.onTheory_model _ _).mp
      (B.is_model.mono Set.subset_union_left)
    let : B ⊨ T := hT
    let N : Theory.ModelType.{u, v, max u v w} T := Theory.ModelType.of T B
    refine ⟨N, fun a => (L.con a : B), fun φ hφ => ?_⟩
    exact (Formula.realize_equivSentence B φ).mp
      (B.is_model.realize_of_mem _ (Or.inr ⟨φ, hφ, rfl⟩))
  · rintro ⟨N, a, ha⟩
    exact partial_of_realizes p a ha

/-- Compactness with the entire background theory retained in each finite test. -/
theorem partial_iff_finite (T : L.Theory) (p : Set (L.Formula α)) :
    IsPartial T p ↔ ∀ s : Finset (L.Formula α), (↑s : Set _) ⊆ p →
      IsPartial T (↑s : Set (L.Formula α)) := by
  classical
  constructor
  · intro hp s hs
    exact hp.mono (Set.union_subset_union_right _ (Set.image_mono hs))
  · intro hp
    apply Theory.isSatisfiable_iff_isFinitelySatisfiable.mpr
    intro Γ hΓ
    let s := (Γ.filter fun γ => γ ∈ Formula.equivSentence '' p).image
      Formula.equivSentence.symm
    have hs : (↑s : Set (L.Formula α)) ⊆ p := by
      intro φ hφ
      obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hφ
      obtain ⟨ψ, hψ, rfl⟩ := (Finset.mem_filter.mp hγ).2
      simpa using hψ
    let B := (hp s hs).some
    have : B ⊨ (↑Γ : L[[α]].Theory) := by
      constructor
      intro γ hγ
      rcases hΓ hγ with hT | hγp
      · exact B.is_model.realize_of_mem γ (Or.inl hT)
      · have hmem : Formula.equivSentence.symm γ ∈ s :=
          Finset.mem_image.mpr ⟨γ, Finset.mem_filter.mpr ⟨hγ, hγp⟩, rfl⟩
        exact B.is_model.realize_of_mem γ
          (Or.inr ⟨Formula.equivSentence.symm γ, hmem, Equiv.apply_symm_apply _ _⟩)
    exact Theory.Model.isSatisfiable B

/-- Maximal consistent formula collections are exactly the ones deciding every formula. -/
theorem complete_iff_decides (T : L.Theory) (p : Set (L.Formula α)) :
    IsCompletePartial T p ↔ IsPartial T p ∧ ∀ φ, φ ∈ p ∨ φ.not ∈ p := by
  classical
  constructor
  · rintro ⟨hp, hmax⟩
    refine ⟨hp, fun φ => ?_⟩
    obtain ⟨N, a, ha⟩ := (partial_iff_model T p).mp hp
    by_cases hφ : φ.Realize a
    · have hi : IsPartial T (insert φ p) := (partial_iff_model _ _).mpr
        ⟨N, a, fun ψ hψ => by rcases hψ with rfl | hψ; exact hφ; exact ha ψ hψ⟩
      exact Or.inl (hmax _ hi (Set.subset_insert _ _) ▸ Set.mem_insert φ p)
    · have hi : IsPartial T (insert φ.not p) := (partial_iff_model _ _).mpr
        ⟨N, a, fun ψ hψ => by
          rcases hψ with rfl | hψ
          · exact (Formula.realize_not).mpr hφ
          · exact ha ψ hψ⟩
      exact Or.inr (hmax _ hi (Set.subset_insert _ _) ▸ Set.mem_insert φ.not p)
  · rintro ⟨hp, hd⟩
    refine ⟨hp, fun q hq hpq => Set.Subset.antisymm ?_ hpq⟩
    intro φ hφ
    rcases hd φ with hφp | hφnp
    · exact hφp
    · obtain ⟨N, a, ha⟩ := (partial_iff_model T q).mp hq
      exact False.elim ((Formula.realize_not.mp (ha _ (hpq hφnp))) (ha _ hφ))

/-- Every complete type's formula presentation is a partial type. -/
theorem partial_formulas (q : T.CompleteType α) : IsPartial T (formulas q) := by
  exact q.isMaximal.1.mono (Set.union_subset q.subset (by
    rintro γ ⟨φ, hφ, rfl⟩
    exact hφ))

/-- Completion returns an actual shared-syntax mathlib complete type containing the conditions. -/
theorem exists_complete_extension (p : Set (L.Formula α)) (hp : IsPartial T p) :
    ∃ q : T.CompleteType α, p ⊆ formulas q := by
  obtain ⟨N, a, ha⟩ := (partial_iff_model T p).mp hp
  refine ⟨T.typeOf a, fun φ hφ => ?_⟩
  exact Theory.CompleteType.formula_mem_typeOf.mpr (ha φ hφ)

/-- Type membership is truth at the specified tuple, with no change of representation. -/
theorem formulas_typeOf {M : Type w'} [L.Structure M] [Nonempty M] [M ⊨ T]
    (a : α → M) : formulas (T.typeOf a) = {φ | φ.Realize a} := by
  ext φ
  exact Theory.CompleteType.formula_mem_typeOf

/-- A complete type realized by a tuple is exactly that tuple's type. -/
theorem realizes_complete_iff {M : Type w'} [L.Structure M] [Nonempty M] [M ⊨ T]
    (q : T.CompleteType α) (a : α → M) :
    Realizes (formulas q) a ↔ q = T.typeOf a := by
  constructor
  · intro ha
    apply SetLike.ext
    intro γ
    constructor
    · intro hγ
      exact Theory.CompleteType.mem_typeOf.mpr
        (ha (Formula.equivSentence.symm γ) (by
          change Formula.equivSentence (Formula.equivSentence.symm γ) ∈ q.toTheory
          rw [Equiv.apply_symm_apply]
          exact hγ))
    · intro hγ
      by_contra hn
      have hnot : γ.not ∈ q := (q.not_mem_iff γ).mpr hn
      have hf := ha (Formula.equivSentence.symm γ.not) (by
          change Formula.equivSentence (Formula.equivSentence.symm γ.not) ∈ q.toTheory
          rw [Equiv.apply_symm_apply]
          exact hnot)
      have ht := Theory.CompleteType.mem_typeOf.mp hγ
      have hneg : Formula.equivSentence.symm γ.not =
          (Formula.equivSentence.symm γ).not := rfl
      exact (Formula.realize_not.mp (hneg ▸ hf)) ht
  · rintro rfl φ hφ
    exact Theory.CompleteType.formula_mem_typeOf.mp hφ

/-- Logical consequence at the tuple is retained by a complete type. -/
theorem complete_closed (q : T.CompleteType α) (φ : L.Formula α)
    (h : ¬ IsPartial T (insert φ.not (formulas q))) : φ ∈ formulas q := by
  rcases q.mem_or_not_mem (Formula.equivSentence φ) with ht | hf
  · exact ht
  · exfalso
    apply h
    convert partial_formulas q using 1
    exact Set.insert_eq_of_mem hf

/-- This bridge establishes that the human maximal-formula definition is mathlib's type space. -/
theorem complete_iff_mathlib (T : L.Theory) (p : Set (L.Formula α)) :
    IsCompletePartial T p ↔ ∃! q : T.CompleteType α, formulas q = p := by
  constructor
  · rintro ⟨hp, hmax⟩
    obtain ⟨q, hpq⟩ := exists_complete_extension p hp
    have hqp : formulas q = p := hmax _ (partial_formulas q) hpq
    refine ⟨q, hqp, fun r hr => ?_⟩
    apply SetLike.ext
    intro γ
    change γ ∈ r.toTheory ↔ γ ∈ q.toTheory
    have h := Set.ext_iff.mp (hr.trans hqp.symm) (Formula.equivSentence.symm γ)
    simpa only [formulas, Set.mem_preimage, Equiv.apply_symm_apply] using h
  · rintro ⟨q, rfl, _⟩
    apply (complete_iff_decides T (formulas q)).mpr
    refine ⟨partial_formulas q, fun φ => ?_⟩
    rcases q.mem_or_not_mem (Formula.equivSentence φ) with h | h
    · exact Or.inl h
    · right
      change Formula.equivSentence φ.not ∈ q.toTheory
      rw [Formula.equivSentence_not]
      exact h

variable {M : Type w'} [L.Structure M] [Nonempty M] {n : ℕ}

private noncomputable def finiteRequest (s : Finset (L.Formula (Fin n))) : L.Sentence :=
  (Formula.relabel Sum.inr (Formula.iInf (fun φ : s => φ.val))).iExs (Fin n)

omit [Nonempty M] in
private theorem finiteRequest_realize (s : Finset (L.Formula (Fin n))) :
    M ⊨ finiteRequest s ↔ ∃ a : Fin n → M, Realizes (↑s : Set (L.Formula (Fin n))) a := by
  simp only [finiteRequest, Sentence.Realize, Formula.realize_iExs,
    Formula.realize_relabel, Function.comp_def, Sum.elim_inr, Formula.realize_iInf]
  simp only [Realizes, Subtype.forall, Finset.mem_coe]

/-- Relative to a structure's complete theory, finite consistency is tested in that structure. -/
theorem partial_iff_finitelyRealized_completeTheory (p : Set (L.Formula (Fin n))) :
    IsPartial (L.completeTheory M) p ↔ FinitelyRealized M p := by
  constructor
  · intro hp s hs
    obtain ⟨N, a, ha⟩ := (partial_iff_model _ p).mp hp
    have hn : N ⊨ finiteRequest s := (finiteRequest_realize s).mpr
      ⟨a, fun φ hφ => ha φ (hs hφ)⟩
    exact (finiteRequest_realize s).mp
      ((realize_iff_of_model_completeTheory M N (finiteRequest s)).mp hn)
  · intro hp
    apply (partial_iff_finite _ p).mpr
    intro s hs
    obtain ⟨a, ha⟩ := hp s hs
    exact partial_of_realizes (↑s : Set (L.Formula (Fin n))) a ha

/-- Realize finitely compatible conditions, with every old named point kept by the stated map. -/
theorem exists_elementary_realization (p : Set (L.Formula (M ⊕ Fin n)))
    (hp : ∀ s : Finset (L.Formula (M ⊕ Fin n)), (↑s : Set _) ⊆ p →
      ∃ a : Fin n → M, Realizes (↑s : Set (L.Formula (M ⊕ Fin n))) (Sum.elim id a)) :
    ∃ (N : Type (max u v w')) (_ : L.Structure N) (_ : Nonempty N),
      ∃ (f : M ↪ₑ[L] N) (b : Fin n → N), Realizes p (Sum.elim f b) := by
  classical
  let k := L.lhomWithConstantsMap (Sum.inl : M → M ⊕ Fin n)
  let E := k.onTheory (L.elementaryDiagram M)
  let U : L[[M ⊕ Fin n]].Theory := E ∪ {γ | Formula.equivSentence.symm γ ∈ p}
  have hsat : U.IsSatisfiable := by
    apply Theory.isSatisfiable_iff_isFinitelySatisfiable.mpr
    intro Γ hΓ
    let s := (Γ.filter fun γ => Formula.equivSentence.symm γ ∈ p).image
      Formula.equivSentence.symm
    have hs : (↑s : Set (L.Formula (M ⊕ Fin n))) ⊆ p := by
      intro φ hφ
      obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hφ
      exact (Finset.mem_filter.mp hγ).2
    obtain ⟨a, ha⟩ := hp s hs
    let v : M ⊕ Fin n → M := Sum.elim id a
    let : L[[M ⊕ Fin n]].Structure M := Diagrams.namedExpansion v
    let : (L.lhomWithConstants (M ⊕ Fin n)).IsExpansionOn M :=
      Diagrams.namedExpansion_isExpansion v
    let : k.IsExpansionOn M := by
      constructor
      · intro m g xs
        cases g with
        | inl g => rfl
        | inr g =>
          cases m with
          | zero => rfl
          | succ m => exact g.elim
      · intro m R xs
        cases R with
        | inl R => rfl
        | inr R => exact R.elim
    have : M ⊨ (↑Γ : L[[M ⊕ Fin n]].Theory) := by
      constructor
      intro γ hγ
      rcases hΓ hγ with he | hpγ
      · obtain ⟨δ, hδ, rfl⟩ := he
        exact (LHom.realize_onSentence M k δ).mpr hδ
      · have hmem : Formula.equivSentence.symm γ ∈ s :=
          Finset.mem_image.mpr ⟨γ, Finset.mem_filter.mpr ⟨hγ, hpγ⟩, rfl⟩
        exact (Formula.realize_equivSentence_symm_con M γ).mp (ha _ hmem)
    exact Theory.Model.isSatisfiable M
  let N := hsat.some
  let : L.Structure N := (L.lhomWithConstants (M ⊕ Fin n)).reduct N
  let : (L.lhomWithConstants (M ⊕ Fin n)).IsExpansionOn N :=
    LHom.isExpansionOn_reduct _ _
  let : L[[M]].Structure N := k.reduct N
  let : (L.lhomWithConstants M).IsExpansionOn N :=
    ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  have hE : N ⊨ E := N.is_model.mono Set.subset_union_left
  let : N ⊨ L.elementaryDiagram M := (LHom.onTheory_model _ _).mp hE
  let f : M ↪ₑ[L] N := ElementaryEmbedding.ofModelsElementaryDiagram L M N
  let b : Fin n → N := fun i => (L.con (Sum.inr i : M ⊕ Fin n) : N)
  refine ⟨N, inferInstance, inferInstance, f, b, fun φ hφ => ?_⟩
  have hn : N ⊨ Formula.equivSentence φ :=
    N.is_model.realize_of_mem _ (Or.inr (by simpa using hφ))
  have hr := (Formula.realize_equivSentence N φ).mp hn
  convert hr using 1
  funext x
  cases x <;> rfl

/-- Turn named parameters into old-element free names while keeping the tuple variables. -/
def parameterFormula (A : Set M) (φ : L[[A]].Formula (Fin n)) :
    L.Formula (M ⊕ Fin n) :=
  Formula.relabel (Sum.map Subtype.val id) (BoundedFormula.constantsVarsEquiv φ)

omit [Nonempty M] in
/-- The parameter translation denotes the original formula with names interpreted by `f`. -/
theorem parameterFormula_realize {N : Type z} [L.Structure N]
    (f : M ↪ₑ[L] N) (A : Set M) (φ : L[[A]].Formula (Fin n)) (b : Fin n → N) :
    (parameterFormula A φ).Realize (Sum.elim f b) ↔
      @Formula.Realize _ (f.toEmbedding.withConstants A) _ _ φ b := by
  rw [parameterFormula, Formula.realize_relabel]
  have hv : (Sum.elim f b) ∘ Sum.map (Subtype.val : A → M) id =
      Sum.elim (fun a : A => f a) b := by
    funext x
    cases x <;> rfl
  rw [hv]
  convert (BoundedFormula.realize_constantsVarsEquiv (M := f.toEmbedding.withConstants A)
      (φ := φ) (v := b) (xs := default)) using 1
  · rfl
  · rfl

/-- The elementary-extension realization criterion for the original language with parameters. -/
theorem parameter_realization (A : Set M) (p : Set (L[[A]].Formula (Fin n))) :
    FinitelyRealized M p ↔
      ∃ (N : Type (max u v w')) (_ : L.Structure N) (_ : Nonempty N),
        ∃ (f : M ↪ₑ[L] N) (b : Fin n → N),
          @Realizes _ _ (f.toEmbedding.withConstants A) _ p b := by
  classical
  constructor
  · intro hp
    let p' := parameterFormula A '' p
    have hp' : ∀ s : Finset (L.Formula (M ⊕ Fin n)), (↑s : Set _) ⊆ p' →
        ∃ a : Fin n → M, Realizes (↑s : Set (L.Formula (M ⊕ Fin n))) (Sum.elim id a) := by
      intro s hs
      let pick (ψ : s) : L[[A]].Formula (Fin n) := Classical.choose (hs ψ.prop)
      have hpick (ψ : s) : pick ψ ∈ p ∧ parameterFormula A (pick ψ) = ψ :=
        Classical.choose_spec (hs ψ.prop)
      let t := s.attach.image pick
      obtain ⟨a, ha⟩ := hp t (by
        rintro φ hφ
        obtain ⟨ψ, _, rfl⟩ := Finset.mem_image.mp hφ
        exact (hpick ψ).1)
      refine ⟨a, fun ψ hψ => ?_⟩
      let ψ' : s := ⟨ψ, hψ⟩
      have ht : pick ψ' ∈ t := Finset.mem_image.mpr ⟨ψ', Finset.mem_attach _ _, rfl⟩
      have hr := (parameterFormula_realize (ElementaryEmbedding.refl L M) A
        (pick ψ') a).mpr (ha _ ht)
      change (parameterFormula A (pick ψ')).Realize (Sum.elim id a) at hr
      rw [(hpick ψ').2] at hr
      exact hr
    obtain ⟨N, SN, hN, f, b, hb⟩ := exists_elementary_realization p' hp'
    let := SN
    let := hN
    refine ⟨N, SN, hN, f, b, fun φ hφ => ?_⟩
    exact (parameterFormula_realize f A φ b).mp (hb _ ⟨φ, hφ, rfl⟩)
  · rintro ⟨N, SN, hN, f, b, hb⟩ s hs
    let := SN
    let := hN
    have ht : f.toEmbedding.withConstants A ⊨ finiteRequest s :=
      (finiteRequest_realize s).mpr ⟨b, fun φ hφ => hb φ (hs hφ)⟩
    exact (finiteRequest_realize s).mp
      (((f.liftWithConstants A).map_sentence (finiteRequest s)).mpr ht)

omit [Nonempty M] in
/-- Applying an elementary embedding keeps the complete type, with its parameter names. -/
theorem parameter_type_transport {N : Type z} [L.Structure N]
    (f : M ↪ₑ[L] N) (A : Set M) (a : Fin n → M) (φ : L[[A]].Formula (Fin n)) :
    φ.Realize a ↔
      @Formula.Realize _ (f.toEmbedding.withConstants A) _ _ φ (f ∘ a) := by
  exact ((f.liftWithConstants A).map_formula φ a).symm

/-- View conditions in a larger parameter language by the indicated inclusion of names. -/
def restrictFormulas {A B : Set M} (h : A ⊆ B)
    (p : Set (L[[B]].Formula (Fin n))) : Set (L[[A]].Formula (Fin n)) :=
  (L.lhomWithConstantsMap (Set.inclusion h)).onBoundedFormula ⁻¹' p

/-- Parameter restriction is itself a complete shared-language type, via the formula bridge. -/
theorem restriction_complete {A B : Set M} (h : A ⊆ B)
    (q : (L[[B]].completeTheory M).CompleteType (Fin n)) :
    IsCompletePartial (L[[A]].completeTheory M) (restrictFormulas h (formulas q)) := by
  classical
  let k := L.lhomWithConstantsMap (Set.inclusion h)
  have hq := (partial_iff_finitelyRealized_completeTheory (M := M) (formulas q)).mp
    (partial_formulas q)
  apply (complete_iff_decides _ _).mpr
  constructor
  · apply (partial_iff_finitelyRealized_completeTheory _).mpr
    intro s hs
    let t := s.image k.onBoundedFormula
    obtain ⟨a, ha⟩ := hq t (by
      rintro ψ hψ
      obtain ⟨φ, hφ, rfl⟩ := Finset.mem_image.mp hψ
      exact hs hφ)
    refine ⟨a, fun φ hφ => ?_⟩
    exact (LHom.realize_onBoundedFormula k φ).mp
      (ha _ (Finset.mem_image.mpr ⟨φ, hφ, rfl⟩))
  · intro φ
    rcases q.mem_or_not_mem (Formula.equivSentence (k.onBoundedFormula φ)) with hf | hn
    · exact Or.inl hf
    · exact Or.inr hn

/-- The restriction of a tuple type is its type with only the retained parameter names. -/
theorem restriction_typeOf {A B : Set M} (h : A ⊆ B) (a : Fin n → M) :
    restrictFormulas h (formulas ((L[[B]].completeTheory M).typeOf a)) =
      formulas ((L[[A]].completeTheory M).typeOf a) := by
  ext φ
  change Formula.equivSentence
      ((L.lhomWithConstantsMap (Set.inclusion h)).onBoundedFormula φ) ∈
      (L[[B]].completeTheory M).typeOf a ↔
    Formula.equivSentence φ ∈ (L[[A]].completeTheory M).typeOf a
  rw [Theory.CompleteType.formula_mem_typeOf, Theory.CompleteType.formula_mem_typeOf]
  exact LHom.realize_onBoundedFormula _ _

/-- Every type over the smaller named subset extends over the larger subset of the same model. -/
theorem restriction_surjective {A B : Set M} (h : A ⊆ B)
    (p : (L[[A]].completeTheory M).CompleteType (Fin n)) :
    ∃ q : (L[[B]].completeTheory M).CompleteType (Fin n),
      restrictFormulas h (formulas q) = formulas p := by
  have hp := (partial_iff_finitelyRealized_completeTheory (M := M) (formulas p)).mp
    (partial_formulas p)
  obtain ⟨N, SN, hN, f, b, hb⟩ := (parameter_realization A (formulas p)).mp hp
  let := SN
  let := hN
  let P := f.toEmbedding.withConstants B
  let : Nonempty P := hN
  let : (constantsOn A).Structure P := constantsOn.structure (fun a : A => f a)
  let : L[[A]].Structure P := inferInstance
  let : P ⊨ L[[A]].completeTheory M :=
    ((f.liftWithConstants A).theory_model_iff _).mp inferInstance
  let : P ⊨ L[[B]].completeTheory M :=
    ((f.liftWithConstants B).theory_model_iff _).mp inferInstance
  let k := L.lhomWithConstantsMap (Set.inclusion h)
  let : k.IsExpansionOn P := by
    constructor
    · intro r c x
      cases c with
      | inl c => rfl
      | inr c =>
        cases r with
        | zero => rfl
        | succ r => exact isEmptyElim c
    · intro r c x
      cases c with
      | inl c => rfl
      | inr c => exact isEmptyElim c
  let b' : Fin n → P := b
  have hb' : Realizes (formulas p) b' := hb
  have hpa := (realizes_complete_iff p b').mp hb'
  refine ⟨(L[[B]].completeTheory M).typeOf (M := P) b', ?_⟩
  rw [hpa]
  ext φ
  change Formula.equivSentence (k.onBoundedFormula φ) ∈
      (L[[B]].completeTheory M).typeOf (M := P) b' ↔
    Formula.equivSentence φ ∈ (L[[A]].completeTheory M).typeOf (M := P) b'
  rw [Theory.CompleteType.formula_mem_typeOf, Theory.CompleteType.formula_mem_typeOf]
  exact LHom.realize_onBoundedFormula k φ

omit [Nonempty M] in
/-- Finite models realize every finitely realizable finite-tuple condition set. -/
theorem finite_realization [Finite M] (p : Set (L.Formula (Fin n)))
    (hp : FinitelyRealized M p) : ∃ a : Fin n → M, Realizes p a := by
  classical
  let := Fintype.ofFinite M
  by_contra h
  have hbad : ∀ a : Fin n → M, ∃ φ ∈ p, ¬ φ.Realize a := by
    intro a
    have hn : ¬ Realizes p a := fun ha => h ⟨a, ha⟩
    simpa only [Realizes, not_forall, not_imp, exists_prop] using hn
  choose φ hφ hbad using hbad
  let s := Finset.univ.image φ
  obtain ⟨a, ha⟩ := hp s (by
    rintro ψ hψ
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hψ
    exact hφ b)
  exact hbad a (ha _ (Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩))

/-- Remove the vacuous fresh names from a complete zero-type. -/
def zeroTheory (q : T.CompleteType (Fin 0)) : L.Theory :=
  (LEquiv.addEmptyConstants L (Fin 0)).symm.toLHom.onTheory q.toTheory

private theorem zeroTheory_named (q : T.CompleteType (Fin 0)) :
    (L.lhomWithConstants (Fin 0)).onTheory (zeroTheory q) = q.toTheory := by
  let e := (LEquiv.addEmptyConstants L (Fin 0)).onSentence
  change e '' (e.symm '' q.toTheory) = q.toTheory
  simp

private theorem zeroTheory_mem (q : T.CompleteType (Fin 0)) (σ : L.Sentence) :
    σ ∈ zeroTheory q ↔ (L.lhomWithConstants (Fin 0)).onSentence σ ∈ q.toTheory := by
  let e := (LEquiv.addEmptyConstants L (Fin 0)).onSentence
  change σ ∈ e.symm '' q.toTheory ↔ e σ ∈ q.toTheory
  exact Set.mem_image_equiv

/-- Zero-types are exactly maximal satisfiable sentence theories extending the background theory. -/
theorem zero_types_iff_complete_extension (S : L.Theory) :
    (∃ q : T.CompleteType (Fin 0), zeroTheory q = S) ↔ T ⊆ S ∧ S.IsMaximal := by
  constructor
  · rintro ⟨q, rfl⟩
    refine ⟨fun σ hσ => (zeroTheory_mem q σ).mpr (q.subset ⟨σ, hσ, rfl⟩), ?_⟩
    constructor
    · apply Theory.isSatisfiable_of_isSatisfiable_onTheory (L.lhomWithConstants (Fin 0))
      rw [zeroTheory_named]
      exact q.isMaximal.1
    · intro σ
      rcases q.mem_or_not_mem ((L.lhomWithConstants (Fin 0)).onSentence σ) with h | h
      · exact Or.inl ((zeroTheory_mem q σ).mpr h)
      · exact Or.inr ((zeroTheory_mem q σ.not).mpr h)
  · rintro ⟨hTS, hS⟩
    let e := (LEquiv.addEmptyConstants L (Fin 0)).onSentence
    let U := (L.lhomWithConstants (Fin 0)).onTheory S
    have hU : U.IsMaximal := by
      constructor
      · exact (Theory.isSatisfiable_onTheory_iff
          (L.lhomWithConstants_injective (Fin 0))).mpr hS.1
      · intro γ
        rcases hS.mem_or_not_mem (e.symm γ) with h | h
        · left
          exact ⟨e.symm γ, h, e.apply_symm_apply γ⟩
        · right
          refine ⟨(e.symm γ).not, h, ?_⟩
          change (e (e.symm γ)).not = γ.not
          rw [e.apply_symm_apply]
    let q : T.CompleteType (Fin 0) :=
      ⟨U, Set.image_mono hTS, hU⟩
    refine ⟨q, ?_⟩
    change e.symm '' (e '' S) = S
    simp

/-- For the complete theory of a fixed structure, all zero-types give its sentence theory. -/
theorem zero_type_unique
    (q r : (L.completeTheory M).CompleteType (Fin 0)) : q = r := by
  have hsame (p : (L.completeTheory M).CompleteType (Fin 0)) :
      zeroTheory p = L.completeTheory M := by
    obtain ⟨hsub, hs⟩ := (zero_types_iff_complete_extension (zeroTheory p)).mp ⟨p, rfl⟩
    apply Set.Subset.antisymm _ hsub
    intro σ hσ
    by_contra hn
    have hneg := ((completeTheory.isMaximal L M).mem_or_not_mem σ).resolve_left hn
    exact Theory.CompleteType.false_of_mem_of_not_mem hs.1 hσ (hsub hneg)
  apply SetLike.ext'
  change q.toTheory = r.toTheory
  rw [← zeroTheory_named q, ← zeroTheory_named r, hsame q, hsame r]

end Lemmatheca.ModelTheory.Types
