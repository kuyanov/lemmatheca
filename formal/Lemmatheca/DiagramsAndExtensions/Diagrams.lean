import Lemmatheca.FirstOrderNormalForms.FirstOrderNormalForms
import Lemmatheca.HenkinCompleteness.HenkinCompleteness
import Lemmatheca.ElementarySubmodels.ElementarySubmodels
import Mathlib.ModelTheory.Satisfiability
import Mathlib.Data.Finset.Preimage

open Lemmatheca.MathematicalLogic

/-! Signed diagrams, canonical named-element maps, and countable elementary extensions.
All formulas and theories use mathlib's shared first-order syntax. -/

namespace Lemmatheca.ModelTheory.Diagrams

open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic.FirstOrderNormalForms
open Lemmatheca.MathematicalLogic.FirstOrderProofs

universe u v w w' w''

variable {L : Language.{u, v}} {M : Type w} {N : Type w'}
private theorem named_atomic {α : Type*} {φ : L.Formula α} (h : φ.IsAtomic) :
    (Formula.equivSentence φ).IsAtomic := by
  cases h <;> constructor

private theorem unnamed_atomic {α : Type*} {γ : L[[α]].Sentence} (h : γ.IsAtomic) :
    (Formula.equivSentence.symm γ).IsAtomic := by
  cases h <;> constructor

private theorem named_qf {α : Type*} {φ : L.Formula α} (h : φ.IsQF) :
    (Formula.equivSentence φ).IsQF := by
  induction h with
  | falsum => exact .falsum
  | of_isAtomic h => exact (named_atomic h).isQF
  | imp _ _ ih ih' => exact ih.imp ih'

private theorem unnamed_qf {α : Type*} {γ : L[[α]].Sentence} (h : γ.IsQF) :
    (Formula.equivSentence.symm γ).IsQF := by
  induction h with
  | falsum => exact .falsum
  | of_isAtomic h => exact (unnamed_atomic h).isQF
  | imp _ _ ih ih' => exact ih.imp ih'

private theorem named_literal {α : Type*} {φ : L.Formula α} (h : IsLiteral φ) :
    IsLiteral (Formula.equivSentence φ) := by
  rcases h with h | ⟨θ, hθ, rfl⟩
  · exact Or.inl (named_atomic h)
  · exact Or.inr ⟨Formula.equivSentence θ, named_atomic hθ, rfl⟩

private theorem unnamed_literal {α : Type*} {γ : L[[α]].Sentence} (h : IsLiteral γ) :
    IsLiteral (Formula.equivSentence.symm γ) := by
  rcases h with h | ⟨θ, hθ, rfl⟩
  · exact Or.inl (unnamed_atomic h)
  · exact Or.inr ⟨Formula.equivSentence.symm θ, unnamed_atomic hθ, rfl⟩

private theorem relabel_literal {α β : Type*} {φ : L.Formula α} (h : IsLiteral φ)
    (f : α → β) : IsLiteral (φ.relabel f) := by
  rcases h with h | ⟨θ, hθ, rfl⟩
  · exact Or.inl (h.relabel (Sum.inl ∘ f))
  · have hθ' : (Formula.relabel f θ).IsAtomic := hθ.relabel (Sum.inl ∘ f)
    exact Or.inr ⟨Formula.relabel f θ, hθ', by simp only [Formula.relabel, BoundedFormula.relabel_not]⟩

private theorem finite_parameter_recovery (γ : L[[M]].Sentence) :
    ∃ (n : ℕ) (φ : L.Formula (Fin n)) (a : Fin n → M),
      γ = Formula.equivSentence (φ.relabel a) ∧
      (IsLiteral γ ↔ IsLiteral φ) ∧ (γ.IsQF ↔ φ.IsQF) := by
  classical
  let ψ : L.Formula M := Formula.equivSentence.symm γ
  have hγ : Formula.equivSentence ψ = γ := Equiv.apply_symm_apply _ _
  by_cases hM : Nonempty M
  · let m : M := Classical.choice hM
    let s := ψ.freeVarFinset
    let e := Fintype.equivFin s
    let a : Fin (Fintype.card s + 1) → M := Fin.snoc (Subtype.val ∘ e.symm) m
    let f : M → Fin (Fintype.card s + 1) := fun x =>
      if h : x ∈ s then (e ⟨x, h⟩).castSucc else Fin.last _
    have haf (x : M) (hx : x ∈ s) : a (f x) = x := by
      simp [f, a, hx]
    have hψ : (ψ.relabel f).relabel a = ψ := by
      rw [formula_relabel_relabel, ← formula_subst_vars]
      calc
        ψ.subst (fun x => .var ((a ∘ f) x)) = ψ.subst Term.var :=
          formula_subst_agree ψ _ _ (fun x hx => congrArg Term.var (haf x hx))
        _ = ψ := formula_subst_var ψ
    have heq : γ = Formula.equivSentence ((ψ.relabel f).relabel a) := by rw [hψ, hγ]
    refine ⟨_, ψ.relabel f, a, heq, ?_, ?_⟩
    · constructor
      · intro h
        exact relabel_literal (unnamed_literal h) f
      · intro h
        rw [heq]
        exact named_literal (relabel_literal h a)
    · constructor
      · intro h
        exact (unnamed_qf h).relabel (Sum.inl ∘ f)
      · intro h
        rw [heq]
        exact named_qf (h.relabel (Sum.inl ∘ a))
  · let : IsEmpty M := not_nonempty_iff.mp hM
    let f : M → Fin 0 := isEmptyElim
    let a : Fin 0 → M := Fin.elim0
    have ha : a ∘ f = id := Subsingleton.elim _ _
    have hψ : (ψ.relabel f).relabel a = ψ := by
      rw [formula_relabel_relabel, ha]
      rw [← formula_subst_vars]
      exact formula_subst_var ψ
    have heq : γ = Formula.equivSentence ((ψ.relabel f).relabel a) := by rw [hψ, hγ]
    refine ⟨0, ψ.relabel f, a, heq, ?_, ?_⟩
    · constructor
      · intro h
        exact relabel_literal (unnamed_literal h) f
      · intro h
        rw [heq]
        exact named_literal (relabel_literal h a)
    · constructor
      · intro h
        exact (unnamed_qf h).relabel (Sum.inl ∘ f)
      · intro h
        rw [heq]
        exact named_qf (h.relabel (Sum.inl ∘ a))

variable [L.Structure M] [L.Structure N]

noncomputable section

/-- The particular map determined by the interpretations of all newly added names. -/
def canonicalMap (L : Language.{u, v}) (M : Type w) (N : Type w')
    [L[[M]].Structure N] : M → N := fun a => (L.con a : N)

/-- An original formula with a finite parameter tuple replaced by new constants. -/
def namedFormula {n : ℕ} (φ : L.Formula (Fin n)) (a : Fin n → M) : L[[M]].Sentence :=
  Formula.equivSentence (φ.relabel a)

/-- The expansion giving the added name of `a` the specified value `f a`. -/
@[instance_reducible]
def namedExpansion (f : M → N) : L[[M]].Structure N :=
  @Language.withConstantsStructure L N _ M (constantsOn.structure f)

omit [L.Structure M] in
theorem namedExpansion_isExpansion (f : M → N) :
    letI := namedExpansion (L := L) f
    (L.lhomWithConstants M).IsExpansionOn N := by
  let : (constantsOn M).Structure N := constantsOn.structure f
  exact L.withConstants_expansion M

omit [L.Structure M] in
theorem canonicalMap_namedExpansion (f : M → N) :
    letI := namedExpansion (L := L) f
    canonicalMap L M N = f := by
  rfl

omit [L.Structure M] in
theorem realize_namedFormula [L[[M]].Structure N]
    [(L.lhomWithConstants M).IsExpansionOn N] {n : ℕ}
    (φ : L.Formula (Fin n)) (a : Fin n → M) :
    N ⊨ namedFormula φ a ↔ φ.Realize (canonicalMap L M N ∘ a) := by
  simp [namedFormula, canonicalMap, Formula.realize_relabel, Function.comp_def]

omit [L.Structure M] in
theorem sentence_is_namedFormula (γ : L[[M]].Sentence) :
    ∃ (n : ℕ) (φ : L.Formula (Fin n)) (a : Fin n → M),
      γ = namedFormula φ a ∧
      (IsLiteral γ ↔ IsLiteral φ) ∧ (γ.IsQF ↔ φ.IsQF) := by
  simpa only [namedFormula] using finite_parameter_recovery (L := L) γ

/-- All true atomic sentences; negative information is deliberately absent. -/
def positiveDiagram (L : Language.{u, v}) (M : Type w) [L.Structure M] : L[[M]].Theory :=
  {γ | γ.IsAtomic ∧ M ⊨ γ}

/-- All true positive or negative atomic sentences in the canonically named structure. -/
def signedDiagram (L : Language.{u, v}) (M : Type w) [L.Structure M] : L[[M]].Theory :=
  {γ | IsLiteral γ ∧ M ⊨ γ}

/-- The alternative diagram consisting of every true quantifier-free sentence. -/
def quantifierFreeDiagram (L : Language.{u, v}) (M : Type w) [L.Structure M] :
    L[[M]].Theory := {γ | γ.IsQF ∧ M ⊨ γ}

omit [L.Structure M] in
private theorem namedFormula_atomic {n : ℕ} {φ : L.Formula (Fin n)}
    (hφ : φ.IsAtomic) (a : Fin n → M) : (namedFormula φ a).IsAtomic := by
  cases hφ with
  | equal => exact .equal _ _
  | rel => exact .rel _ _

omit [L.Structure M] in
private theorem namedFormula_literal {n : ℕ} {φ : L.Formula (Fin n)}
    (hφ : IsLiteral φ) (a : Fin n → M) : IsLiteral (namedFormula φ a) := by
  rcases hφ with ha | ⟨θ, hθ, rfl⟩
  · exact Or.inl (namedFormula_atomic ha a)
  · change IsLiteral (Formula.equivSentence ((Formula.relabel a θ).not))
    rw [Formula.equivSentence_not]
    exact Or.inr ⟨_, namedFormula_atomic hθ a, rfl⟩

private theorem literal_isQF {α : Type*} {n : ℕ} {φ : L.BoundedFormula α n}
    (h : IsLiteral φ) : φ.IsQF := by
  rcases h with h | ⟨ψ, hψ, rfl⟩
  · exact h.isQF
  · exact hψ.isQF.not

private theorem hom_preserves_atomic {α : Type*} {n : ℕ}
    (f : M →[L] N) {φ : L.BoundedFormula α n} (hφ : φ.IsAtomic)
    (a : α → M) (xs : Fin n → M) :
    φ.Realize a xs → φ.Realize (f ∘ a) (f ∘ xs) := by
  cases hφ with
  | equal t s =>
    simp only [BoundedFormula.realize_bdEqual, ← Sum.comp_elim, HomClass.realize_term]
    exact congrArg f
  | rel r ts =>
    simp only [BoundedFormula.realize_rel, ← Sum.comp_elim, HomClass.realize_term]
    exact f.map_rel r _

theorem embedding_iff_atomic_agreement (f : M → N) :
    (∃ e : M ↪[L] N, (e : M → N) = f) ↔
      ∀ (n : ℕ) (φ : L.Formula (Fin n)), φ.IsAtomic →
        ∀ a : Fin n → M, φ.Realize a ↔ φ.Realize (f ∘ a) := by
  constructor
  · rintro ⟨e, rfl⟩ n φ hφ a
    simpa only [Formula.Realize, Unique.eq_default] using
      (hφ.isQF.realize_embedding e (v := a) (xs := default)).symm
  · intro ha
    have hf : Function.Injective f := by
      intro a b hab
      have h := (ha 2 ((Term.var (0 : Fin 2)).equal (.var 1))
        (.equal _ _) ![a, b]).mpr
      simpa using h (by simpa using hab)
    refine ⟨{ toFun := f, inj' := hf, map_fun' := ?_, map_rel' := ?_ }, rfl⟩
    · intro n g a
      have h := (ha (n + 1) (Formula.graph g) (Formula.isAtomic_graph g)
        (Fin.cons (Structure.funMap g a) a)).mp (Formula.realize_graph.mpr rfl)
      rw [Fin.comp_cons, Formula.realize_graph] at h
      exact h.symm
    · intro n r a
      exact (ha n (.rel r (fun i => .var (.inl i))) (.rel r _) a).symm

theorem embedding_iff_preserves_literals (f : M → N) :
    (∃ e : M ↪[L] N, (e : M → N) = f) ↔
      ∀ (n : ℕ) (φ : L.Formula (Fin n)), IsLiteral φ →
        ∀ a : Fin n → M, φ.Realize a → φ.Realize (f ∘ a) := by
  rw [embedding_iff_atomic_agreement]
  constructor
  · intro h n φ hφ a ha
    rcases hφ with hφ | ⟨ψ, hψ, rfl⟩
    · exact (h n φ hφ a).mp ha
    · exact fun hb => ha ((h n ψ hψ a).mpr hb)
  · intro h n φ hφ a
    refine ⟨h n φ (Or.inl hφ) a, ?_⟩
    intro hb
    by_contra ha
    exact (h n φ.not (Or.inr ⟨φ, hφ, rfl⟩) a ha) hb

omit [L.Structure N] in
theorem models_signed_iff_models_quantifierFree [L[[M]].Structure N] :
    N ⊨ signedDiagram L M ↔ N ⊨ quantifierFreeDiagram L M := by
  constructor
  · intro h
    have hatom : ∀ γ : L[[M]].Sentence, γ.IsAtomic → (M ⊨ γ ↔ N ⊨ γ) := by
      intro γ hγ
      constructor
      · intro hm
        exact h.realize_of_mem γ ⟨Or.inl hγ, hm⟩
      · intro hn
        by_contra hm
        have hf := h.realize_of_mem γ.not ⟨Or.inr ⟨γ, hγ, rfl⟩, hm⟩
        exact hf hn
    constructor
    intro γ hγ
    have agree : ∀ δ : L[[M]].Sentence, δ.IsQF → (M ⊨ δ ↔ N ⊨ δ) := by
      intro δ hδ
      induction hδ with
      | falsum => rfl
      | of_isAtomic ha => exact hatom _ ha
      | imp _ _ ih1 ih2 =>
        simp only [Sentence.Realize, Formula.realize_imp] at *
        exact imp_congr ih1 ih2
    exact (agree γ hγ.1).mp hγ.2
  · intro h
    exact ⟨fun γ hγ => h.realize_of_mem γ ⟨literal_isQF hγ.1, hγ.2⟩⟩

theorem model_signed_iff_canonical_embedding [L[[M]].Structure N]
    [(L.lhomWithConstants M).IsExpansionOn N] :
    N ⊨ signedDiagram L M ↔
      ∃ e : M ↪[L] N, (e : M → N) = canonicalMap L M N := by
  constructor
  · intro h
    apply (embedding_iff_preserves_literals (canonicalMap L M N)).mpr
    intro n φ hφ a ha
    have hm : M ⊨ namedFormula φ a :=
      (realize_namedFormula (N := M) φ a).mpr ha
    exact (realize_namedFormula φ a).mp
      (h.realize_of_mem _ ⟨namedFormula_literal hφ a, hm⟩)
  · rintro ⟨e, he⟩
    constructor
    intro γ hγ
    obtain ⟨n, φ, a, rfl, hLit, _⟩ := sentence_is_namedFormula γ
    have hm : φ.Realize a := (realize_namedFormula (N := M) φ a).mp hγ.2
    have hn := (embedding_iff_preserves_literals (e : M → N)).mp ⟨e, rfl⟩
      n φ (hLit.mp hγ.1) a hm
    apply (realize_namedFormula φ a).mpr
    simpa only [he] using hn

theorem embedding_namedExpansion_models_signed (e : M ↪[L] N) :
    letI := namedExpansion (L := L) (e : M → N)
    N ⊨ signedDiagram L M := by
  let : L[[M]].Structure N := namedExpansion (L := L) (e : M → N)
  let : (L.lhomWithConstants M).IsExpansionOn N :=
    namedExpansion_isExpansion (e : M → N)
  exact model_signed_iff_canonical_embedding.mpr ⟨e, rfl⟩

theorem hom_namedExpansion_models_positive (f : M →[L] N) :
    letI := namedExpansion (L := L) (f : M → N)
    N ⊨ positiveDiagram L M := by
  let : L[[M]].Structure N := namedExpansion (L := L) (f : M → N)
  let : (L.lhomWithConstants M).IsExpansionOn N :=
    namedExpansion_isExpansion (f : M → N)
  constructor
  intro γ hγ
  let φ : L.Formula M := Formula.equivSentence.symm γ
  have hφ : φ.IsAtomic := by
    rcases hγ.1 with h | h
    · exact .equal _ _
    · exact .rel _ _
  have hm : φ.Realize id := (Formula.realize_equivSentence_symm_con M γ).mpr hγ.2
  have hn := hom_preserves_atomic f hφ id default hm
  apply (Formula.realize_equivSentence_symm_con N γ).mp
  change φ.Realize (f : M → N)
  simpa only [Formula.Realize, Unique.eq_default, Function.comp_id] using hn

theorem signedDiagram_name_ne (a b : M) (hab : a ≠ b) :
    ((Constants.term (L.con a)).equal (Constants.term (L.con b))).not ∈
      signedDiagram L M := by
  refine ⟨Or.inr ⟨_, .equal _ _, rfl⟩, ?_⟩
  change a ≠ b
  exact hab

theorem signedDiagram_function_fact {n : ℕ} (g : L.Functions n) (a : Fin n → M) :
    ((Term.func (Sum.inl g) fun i => Constants.term (L.con (a i))).equal
      (Constants.term (L.con (Structure.funMap g a)))) ∈ signedDiagram L M := by
  refine ⟨Or.inl (.equal _ _), ?_⟩
  change Structure.funMap g a = Structure.funMap g a
  rfl

theorem signedDiagram_relation_fact {n : ℕ} (R : L.Relations n) (a : Fin n → M) :
    let γ : L[[M]].Sentence :=
      Relations.formula (L := L[[M]]) (Sum.inl R) fun i => Constants.term (L.con (a i))
    (Structure.RelMap R a → γ ∈ signedDiagram L M) ∧
      (¬Structure.RelMap R a → γ.not ∈ signedDiagram L M) := by
  dsimp
  constructor
  · intro h
    refine ⟨Or.inl (.rel _ _), ?_⟩
    change Structure.RelMap R a
    exact h
  · intro h
    refine ⟨Or.inr ⟨_, .rel _ _, rfl⟩, ?_⟩
    change ¬Structure.RelMap R a
    exact h

theorem signed_subset_elementary : signedDiagram L M ⊆ L.elementaryDiagram M := by
  exact fun _ h => h.2

theorem diagrams_have_canonical_model :
    M ⊨ signedDiagram L M ∧ M ⊨ L.elementaryDiagram M := by
  exact ⟨⟨fun _ h => h.2⟩, inferInstance⟩

theorem model_elementary_iff_canonical_elementary [L[[M]].Structure N]
    [(L.lhomWithConstants M).IsExpansionOn N] :
    N ⊨ L.elementaryDiagram M ↔
      ∃ e : M ↪ₑ[L] N, (e : M → N) = canonicalMap L M N := by
  constructor
  · intro h
    let := h
    exact ⟨ElementaryEmbedding.ofModelsElementaryDiagram L M N, rfl⟩
  · rintro ⟨e, he⟩
    constructor
    intro γ hγ
    have hm := (Formula.realize_equivSentence_symm_con M γ).mpr hγ
    have hn := (e.map_formula (Formula.equivSentence.symm γ) id).mpr hm
    apply (Formula.realize_equivSentence_symm_con N γ).mp
    change (Formula.equivSentence.symm γ).Realize (canonicalMap L M N)
    simpa only [Function.comp_id, he] using hn

theorem elementary_namedExpansion_models_diagram (e : M ↪ₑ[L] N) :
    letI := namedExpansion (L := L) (e : M → N)
    N ⊨ L.elementaryDiagram M := by
  let : L[[M]].Structure N := namedExpansion (L := L) (e : M → N)
  let : (L.lhomWithConstants M).IsExpansionOn N :=
    namedExpansion_isExpansion (e : M → N)
  exact model_elementary_iff_canonical_elementary.mpr ⟨e, rfl⟩

/-- Relabel an elementary copy along any bijection agreeing with the specified map. -/
theorem transport_elementarity {D : Type w''} (h : M ↪ₑ[L] N) (e : D ≃ N)
    (i : M → D) (hi : ∀ a, e (i a) = h a) :
    letI : L.Structure D := e.symm.inducedStructure
    ∃ j : M ↪ₑ[L] D, (j : M → D) = i := by
  let : L.Structure D := e.symm.inducedStructure
  refine ⟨e.symm.inducedStructureEquiv.toElementaryEmbedding.comp h, ?_⟩
  funext a
  change e.symm (h a) = i a
  exact e.symm_apply_eq.mpr (hi a).symm

/-- Keep the old points as the left summand and label every point outside the image separately. -/
def copyEquiv (h : M ↪ₑ[L] N) : (M ⊕ {b : N // b ∉ Set.range h}) ≃ N := by
  classical
  exact ((Equiv.ofInjective h h.injective).sumCongr (_root_.Equiv.refl _)).trans
    (Equiv.Set.sumCompl (Set.range h))

theorem copyEquiv_old_points (h : M ↪ₑ[L] N) (a : M) :
    copyEquiv h (Sum.inl a) = h a := by
  rfl

theorem elementary_copy_inclusion (h : M ↪ₑ[L] N) :
    letI : L.Structure (M ⊕ {b : N // b ∉ Set.range h}) :=
      (copyEquiv h).symm.inducedStructure
    ∃ j : M ↪ₑ[L] (M ⊕ {b : N // b ∉ Set.range h}),
      (j : M → M ⊕ {b : N // b ∉ Set.range h}) = Sum.inl := by
  exact transport_elementarity h (copyEquiv h) Sum.inl (copyEquiv_old_points h)

theorem copy_nonempty_complement_iff (h : M ↪ₑ[L] N) :
    Nonempty {b : N // b ∉ Set.range h} ↔ ¬Function.Surjective h := by
  constructor
  · rintro ⟨⟨b, hb⟩⟩ hs
    exact hb (hs b)
  · intro hs
    classical
    simp only [Function.Surjective, not_forall] at hs
    obtain ⟨b, hb⟩ := hs
    exact ⟨⟨b, hb⟩⟩

/-- `none` names a new point and `some a` names the original point `a`. -/
def newPointUnequal (a : M) : L[[Option M]].Sentence :=
  ((Constants.term (L.con (none : Option M))).equal
    (Constants.term (L.con (some a)))).not

private theorem newPointUnequal_injective :
    Function.Injective (newPointUnequal (L := L) : M → L[[Option M]].Sentence) := by
  intro a b hab
  by_contra hne
  let : L[[Option M]].Structure M :=
    namedExpansion (L := L) (fun o : Option M => o.elim a id)
  have ha : ¬(M ⊨ newPointUnequal (L := L) a) := by
    change ¬a ≠ a
    simp
  have hb : M ⊨ newPointUnequal (L := L) b := by
    change a ≠ b
    exact hne
  exact ha (hab.symm ▸ hb)

/-- The elementary diagram together with a point distinct from all original names. -/
def properExtensionTheory (L : Language.{u, v}) (M : Type w) [L.Structure M] :
    L[[Option M]].Theory :=
  (L.lhomWithConstantsMap (some : M → Option M)).onTheory (L.elementaryDiagram M) ∪
    Set.range (newPointUnequal (L := L) : M → L[[Option M]].Sentence)

theorem properExtensionTheory_finite_subset_realized [Infinite M]
    (Γ : Finset L[[Option M]].Sentence)
    (hΓ : (↑Γ : L[[Option M]].Theory) ⊆ properExtensionTheory L M) :
    ∃ b : M,
      letI := namedExpansion (L := L) (fun o : Option M => o.elim b id)
      M ⊨ (↑Γ : L[[Option M]].Theory) := by
  classical
  let excluded : Finset M := Γ.preimage (newPointUnequal (L := L))
    newPointUnequal_injective.injOn
  obtain ⟨b, hb⟩ := excluded.exists_notMem
  refine ⟨b, ?_⟩
  let : (constantsOn (Option M)).Structure M :=
    constantsOn.structure (fun o : Option M => o.elim b id)
  let : L[[Option M]].Structure M :=
    namedExpansion (L := L) (fun o : Option M => o.elim b id)
  let : (LHom.constantsOnMap (some : M → Option M)).IsExpansionOn M :=
    constantsOnMap_isExpansionOn (fα := id) (by rfl)
  let : (L.lhomWithConstantsMap (some : M → Option M)).IsExpansionOn M :=
    LHom.sumMap_isExpansionOn _ _ M
  constructor
  intro γ hγ
  rcases hΓ hγ with hdiag | hneq
  · obtain ⟨φ, hφ, rfl⟩ := hdiag
    exact (LHom.realize_onSentence (M := M)
      (L.lhomWithConstantsMap (some : M → Option M)) φ).mpr hφ
  · obtain ⟨a, rfl⟩ := hneq
    have ha : a ∈ excluded := by simpa [excluded] using hγ
    change b ≠ a
    exact fun h => hb (h.symm ▸ ha)

theorem properExtensionTheory_finitelySatisfiable [Infinite M] :
    (properExtensionTheory L M).IsFinitelySatisfiable := by
  intro Γ hΓ
  obtain ⟨b, hb⟩ := properExtensionTheory_finite_subset_realized Γ hΓ
  let : L[[Option M]].Structure M :=
    namedExpansion (L := L) (fun o : Option M => o.elim b id)
  let := hb
  exact Theory.Model.isSatisfiable M

theorem properExtensionTheory_model_iff [L[[Option M]].Structure N]
    [(L.lhomWithConstants (Option M)).IsExpansionOn N] :
    N ⊨ properExtensionTheory L M ↔
      (∃ e : M ↪ₑ[L] N, (e : M → N) = fun a => (L.con (some a) : N)) ∧
        ∀ a : M, (L.con (none : Option M) : N) ≠ (L.con (some a) : N) := by
  let k := L.lhomWithConstantsMap (some : M → Option M)
  let : L[[M]].Structure N := k.reduct N
  let : (L.lhomWithConstants M).IsExpansionOn N :=
    ⟨fun g x => (L.lhomWithConstants (Option M)).map_onFunction g x,
      fun R x => (L.lhomWithConstants (Option M)).map_onRelation R x⟩
  constructor
  · intro hU
    have hOld : N ⊨ L.elementaryDiagram M :=
      (LHom.onTheory_model k _).mp (hU.mono Set.subset_union_left)
    obtain ⟨e, he⟩ := model_elementary_iff_canonical_elementary.mp hOld
    refine ⟨⟨e, he⟩, ?_⟩
    intro a
    have h := hU.realize_of_mem (newPointUnequal a) (Or.inr ⟨a, rfl⟩)
    simpa only [newPointUnequal, Sentence.Realize, Formula.realize_not,
      Formula.realize_equal, Term.realize_constants] using h
  · rintro ⟨⟨e, he⟩, hnew⟩
    have hOld : N ⊨ L.elementaryDiagram M :=
      model_elementary_iff_canonical_elementary.mpr ⟨e, he⟩
    refine ((LHom.onTheory_model k _).mpr hOld).union ⟨?_⟩
    intro γ hγ
    obtain ⟨a, rfl⟩ := hγ
    simpa only [newPointUnequal, Sentence.Realize, Formula.realize_not,
      Formula.realize_equal, Term.realize_constants] using hnew a

theorem exists_proper_countable_elementary_extension [Countable L.Symbols]
    [Countable M] [Infinite M] :
    ∃ (N : Type (max u v w)) (_ : L.Structure N), Countable N ∧ Infinite N ∧
      ∃ (h : M ↪ₑ[L] N) (b : N), ∀ a : M, h a ≠ b := by
  have hsat : (properExtensionTheory L M).IsSatisfiable :=
    Theory.isSatisfiable_iff_isFinitelySatisfiable.mpr
      properExtensionTheory_finitelySatisfiable
  obtain ⟨A⟩ := hsat
  have hcon := theory_consistent_of_model A.is_model
  obtain ⟨N, hstr, hne, hc, hmodel⟩ :=
    HenkinCompleteness.countable_model_existence hcon
  let : L[[Option M]].Structure N := hstr
  let : L.Structure N := (L.lhomWithConstants (Option M)).reduct N
  obtain ⟨⟨h, he⟩, hnew⟩ := properExtensionTheory_model_iff.mp hmodel
  have hInf : Infinite N := Infinite.of_injective h h.injective
  refine ⟨N, inferInstance, hc, hInf, h, (L.con (none : Option M) : N), ?_⟩
  intro a ha
  exact hnew a (ha.symm.trans (congrFun he a))

theorem finite_elementary_embedding_surjective [Finite M] (h : M ↪ₑ[L] N) :
    Function.Surjective h := by
  classical
  let ψ : L.BoundedFormula M 1 := BoundedFormula.iSup fun a : M =>
    (.var (.inr 0) : L.Term (M ⊕ Fin 1)).bdEqual (.var (.inl a))
  let φ : L.Formula M := ψ.all
  have hm : φ.Realize id := by
    simp [φ, ψ, Formula.Realize, BoundedFormula.realize_iSup]
  have hn := (h.map_formula φ id).mpr hm
  have hcover : ∀ b : N, ∃ a : M, b = h a := by
    simpa [φ, ψ, Formula.Realize, BoundedFormula.realize_iSup, Fin.snoc_zero] using hn
  intro b
  obtain ⟨a, ha⟩ := hcover b
  exact ⟨a, ha.symm⟩

theorem finite_properExtensionTheory_unsatisfiable [Finite M] [Nonempty M] :
    ¬(properExtensionTheory L M).IsSatisfiable := by
  rintro ⟨N⟩
  let : L.Structure N := (L.lhomWithConstants (Option M)).reduct N
  obtain ⟨⟨h, he⟩, hnew⟩ := properExtensionTheory_model_iff.mp N.is_model
  obtain ⟨a, ha⟩ := finite_elementary_embedding_surjective h
    (L.con (none : Option M) : N)
  exact hnew a (ha.symm.trans (congrFun he a))

theorem finite_obstruction_fragment [Finite M] [Nonempty M] :
    ∃ Γ : Finset L[[Option M]].Sentence,
      (↑Γ : L[[Option M]].Theory) ⊆ properExtensionTheory L M ∧
        ¬Theory.IsSatisfiable (↑Γ : L[[Option M]].Theory) := by
  classical
  by_contra h
  apply finite_properExtensionTheory_unsatisfiable (L := L) (M := M)
  apply Theory.isSatisfiable_iff_isFinitelySatisfiable.mpr
  intro Γ hΓ
  by_contra hs
  exact h ⟨Γ, hΓ, hs⟩

/-- The sentence saying that every point is one of the named elements of the finite structure. -/
def namedCoverSentence (L : Language.{u, v}) (M : Type w) [Finite M] : L[[M]].Sentence :=
  (BoundedFormula.iSup fun a : M =>
    (.var (.inr 0) : L[[M]].Term (Empty ⊕ Fin 1)).bdEqual
      (Constants.term (L.con a))).all

/-- The specified finite obstruction: the named covering sentence and every new-point inequality.
The old names are included in the language with the extra `none` name by `some`. -/
def exactFiniteObstruction (L : Language.{u, v}) (M : Type w) [Finite M] :
    Finset L[[Option M]].Sentence := by
  classical
  letI := Fintype.ofFinite M
  exact insert ((L.lhomWithConstantsMap (some : M → Option M)).onSentence
      (namedCoverSentence L M))
    (Finset.univ.image (newPointUnequal (L := L) : M → L[[Option M]].Sentence))

theorem exactFiniteObstruction_subset [Finite M] [Nonempty M] :
    (↑(exactFiniteObstruction L M) : L[[Option M]].Theory) ⊆
      properExtensionTheory L M := by
  classical
  intro γ hγ
  change γ ∈ exactFiniteObstruction L M at hγ
  simp only [exactFiniteObstruction, Finset.mem_insert, Finset.mem_image,
    Finset.mem_univ, true_and] at hγ
  rcases hγ with rfl | ⟨a, rfl⟩
  · refine Or.inl ⟨namedCoverSentence L M, ?_, rfl⟩
    change M ⊨ namedCoverSentence L M
    simp [namedCoverSentence, Sentence.Realize, Formula.Realize,
      BoundedFormula.realize_iSup, Fin.snoc_zero]
    intro a
    exact ⟨a, rfl⟩
  · exact Or.inr ⟨a, rfl⟩

omit [L.Structure M] in
theorem exactFiniteObstruction_unsatisfiable [_sourceStructure : L.Structure M]
    [Finite M] [Nonempty M] :
    ¬Theory.IsSatisfiable (↑(exactFiniteObstruction L M) : L[[Option M]].Theory) := by
  classical
  rintro ⟨N⟩
  let k := L.lhomWithConstantsMap (some : M → Option M)
  have hcover : N ⊨ k.onSentence (namedCoverSentence L M) :=
    N.is_model.realize_of_mem _ (by simp [exactFiniteObstruction, k])
  let : L[[M]].Structure N := k.reduct N
  have hold : N ⊨ namedCoverSentence L M :=
    (LHom.realize_onSentence N k _).mp hcover
  have hallOld : ∀ b : N, ∃ a : M, b = (L.con a : N) := by
    simpa [namedCoverSentence, Sentence.Realize, Formula.Realize,
      BoundedFormula.realize_iSup, Fin.snoc_zero] using hold
  have hall : ∀ b : N, ∃ a : M, b = (L.con (some a) : N) := by
    intro b
    obtain ⟨a, ha⟩ := hallOld b
    exact ⟨a, ha⟩
  obtain ⟨a, ha⟩ := hall (L.con (none : Option M) : N)
  have hne : N ⊨ newPointUnequal (L := L) a :=
    N.is_model.realize_of_mem _ (by simp [exactFiniteObstruction])
  have hne' : (L.con (none : Option M) : N) ≠ (L.con (some a) : N) := by
    simpa only [newPointUnequal, Sentence.Realize, Formula.realize_not,
      Formula.realize_equal, Term.realize_constants] using hne
  exact hne' ha

end
end Lemmatheca.ModelTheory.Diagrams
