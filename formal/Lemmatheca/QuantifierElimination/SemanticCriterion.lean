import Lemmatheca.QuantifierElimination.QuantifierEliminationShared
import Mathlib.ModelTheory.Satisfiability

/-! Semantic quantifier elimination in actual shared first-order syntax.

The two compactness steps produce finite conjunctions and disjunctions of native
formulas. The final criterion uses the existing `HasQuantifierElimination`, not
an assumed preservation or compactness principle.
-/
namespace Lemmatheca.ModelTheory.QuantifierElimination.Semantic

open FirstOrder FirstOrder.Language

universe u v w w'
variable {L : Language.{u, v}}

/-- Agreement on all quantifier-free formulas in the same finite free context. -/
def QFAgree {n : ℕ} {M : Type w} {N : Type w'}
    [L.Structure M] [L.Structure N] (a : Fin n → M) (b : Fin n → N) : Prop :=
  ∀ θ : L.Formula (Fin n), θ.IsQF → (θ.Realize a ↔ θ.Realize b)

/-- Agreement on all formulas in the same finite free context. -/
def FullAgree {n : ℕ} {M : Type w} {N : Type w'}
    [L.Structure M] [L.Structure N] (a : Fin n → M) (b : Fin n → N) : Prop :=
  ∀ θ : L.Formula (Fin n), θ.Realize a ↔ θ.Realize b

/-- The complete signed quantifier-free description of a tuple. -/
def qfDescription {n : ℕ} {M : Type w} [L.Structure M] (a : Fin n → M) :
    Set (L.Formula (Fin n)) := {θ | θ.IsQF ∧ θ.Realize a}

/-- A formula's truth depends only on the quantifier-free information. -/
def QFInvariant (T : L.Theory) {n : ℕ} (φ : L.Formula (Fin n)) : Prop :=
  ∀ (M N : Theory.ModelType.{u, v, max u v w} T)
    (a : Fin n → M) (b : Fin n → N), QFAgree (L := L) a b → (φ.Realize a ↔ φ.Realize b)

/-- A genuine finite formula, including the empty conjunction. -/
def finiteConjunction {n : ℕ} (l : List (L.Formula (Fin n))) : L.Formula (Fin n) :=
  l.foldr (· ⊓ ·) ⊤

/-- A genuine finite formula, including the empty disjunction. -/
def finiteDisjunction {n : ℕ} (l : List (L.Formula (Fin n))) : L.Formula (Fin n) :=
  l.foldr (· ⊔ ·) ⊥

theorem description_agreement {n : ℕ} {M : Type w} {N : Type w'}
    [L.Structure M] [L.Structure N] (a : Fin n → M) (b : Fin n → N) :
    (∀ θ ∈ qfDescription (L := L) a, θ.Realize b) ↔ QFAgree (L := L) a b := by
  classical
  constructor
  · intro h θ hθ
    constructor
    · intro ha
      exact h θ ⟨hθ, ha⟩
    · intro hb
      by_contra ha
      have hn := h θ.not ⟨hθ.not, Formula.realize_not.mpr ha⟩
      exact (Formula.realize_not.mp hn) hb
  · intro h θ hθ
    exact (h θ hθ.1).mp hθ.2

private theorem finiteConjunction_isQF {n : ℕ} (l : List (L.Formula (Fin n)))
    (hl : ∀ θ ∈ l, θ.IsQF) : (finiteConjunction l).IsQF := by
  induction l with
  | nil => exact BoundedFormula.IsQF.top
  | cons θ l ih =>
    exact (hl θ (by simp)).inf (ih (fun ψ hψ => hl ψ (by simp [hψ])))

private theorem finiteDisjunction_isQF {n : ℕ} (l : List (L.Formula (Fin n)))
    (hl : ∀ θ ∈ l, θ.IsQF) : (finiteDisjunction l).IsQF := by
  induction l with
  | nil => exact BoundedFormula.isQF_bot
  | cons θ l ih =>
    exact (hl θ (by simp)).sup (ih (fun ψ hψ => hl ψ (by simp [hψ])))

/-- The first compactness step: a finite subset of the actual description suffices. -/
theorem finite_qf_neighborhood {T : L.Theory} {n : ℕ} {φ : L.Formula (Fin n)}
    (hφ : QFInvariant.{u, v, w} T φ)
    (M : Theory.ModelType.{u, v, max u v w} T) (a : Fin n → M)
    (ha : φ.Realize a) :
    ∃ l : List (L.Formula (Fin n)),
      (∀ θ ∈ l, θ ∈ qfDescription (L := L) a) ∧
      (finiteConjunction l).IsQF ∧ (finiteConjunction l).Realize a ∧
      T ⊨ᵇ ((finiteConjunction l).imp φ) := by
  classical
  let lhom := L.lhomWithConstants (Fin n)
  let G : L[[Fin n]].Theory :=
    {γ | ∃ θ ∈ qfDescription (L := L) a, γ = Formula.equivSentence θ}
  let U : L[[Fin n]].Theory := lhom.onTheory T ∪ G
  have hUφ : U ⊨ᵇ Formula.equivSentence φ := by
    apply Theory.models_sentence_iff.mpr
    intro A
    let : L.Structure A := lhom.reduct A
    let : lhom.IsExpansionOn A := LHom.isExpansionOn_reduct _ _
    have hAT : A ⊨ T :=
      (LHom.onTheory_model lhom T).mp (A.is_model.mono Set.subset_union_left)
    let : A ⊨ T := hAT
    let N : Theory.ModelType.{u, v, max u v} T := Theory.ModelType.of T A
    let b : Fin n → N := fun i => (L.con i : A)
    have hdesc : ∀ θ ∈ qfDescription (L := L) a, θ.Realize b := by
      intro θ hθ
      apply (Formula.realize_equivSentence A θ).mp
      exact A.is_model.realize_of_mem _ (Or.inr ⟨θ, hθ, rfl⟩)
    let N' : Theory.ModelType.{u, v, max u v w} T := N.ulift
    let e : N ≃[L] N' := (_root_.Equiv.ulift.symm : N ≃ N').inducedStructureEquiv
    have hagree : QFAgree (L := L) a (e ∘ b) := by
      intro θ hθ
      exact (((description_agreement (L := L) a b).mp hdesc) θ hθ).trans
        (e.toElementaryEmbedding.map_formula θ b).symm
    have hφb : φ.Realize b :=
      (e.toElementaryEmbedding.map_formula φ b).mp ((hφ M N' a (e ∘ b) hagree).mp ha)
    exact (Formula.realize_equivSentence A φ).mpr hφb
  obtain ⟨Δ, hΔ, hΔφ⟩ := Theory.models_iff_finset_models.mp hUφ
  let B := Δ.filter (· ∈ G)
  have hb (γ : {γ // γ ∈ B}) :
      ∃ θ ∈ qfDescription (L := L) a, γ.val = Formula.equivSentence θ :=
    (Finset.mem_filter.mp γ.property).2
  let chooseθ (γ : {γ // γ ∈ B}) : L.Formula (Fin n) := Classical.choose (hb γ)
  have hchoose (γ : {γ // γ ∈ B}) := Classical.choose_spec (hb γ)
  let l : List (L.Formula (Fin n)) := B.attach.toList.map chooseθ
  have hl (θ : L.Formula (Fin n)) (hθ : θ ∈ l) :
      θ ∈ qfDescription (L := L) a := by
    obtain ⟨γ, _, rfl⟩ := List.mem_map.mp hθ
    exact (hchoose γ).1
  refine ⟨l, hl, finiteConjunction_isQF l (fun θ hθ => (hl θ hθ).1), ?_, ?_⟩
  · exact (BoundedFormula.realize_foldr_inf l a default).mpr (fun θ hθ => (hl θ hθ).2)
  · apply Theory.models_formula_iff.mpr
    intro N b
    rw [Formula.realize_imp]
    intro hbφ
    have hbl := (BoundedFormula.realize_foldr_inf l b default).mp hbφ
    let : (constantsOn (Fin n)).Structure N := constantsOn.structure b
    have hmodel : N ⊨ (↑Δ : L[[Fin n]].Theory) := by
      constructor
      intro γ hγ
      rcases hΔ hγ with hγT | hγG
      · obtain ⟨δ, hδ, rfl⟩ := hγT
        apply (LHom.realize_onSentence N lhom δ).mpr
        exact N.is_model.realize_of_mem δ hδ
      · have hγB : γ ∈ B := Finset.mem_filter.mpr ⟨hγ, hγG⟩
        let γB : {γ // γ ∈ B} := ⟨γ, hγB⟩
        have hmem : chooseθ γB ∈ l := List.mem_map.mpr ⟨γB, by simp, rfl⟩
        change N ⊨ γB.val
        rw [(hchoose γB).2]
        exact (Formula.realize_equivSentence N _).mpr (hbl _ hmem)
    let : N ⊨ (↑Δ : L[[Fin n]].Theory) := hmodel
    exact (Formula.realize_equivSentence N φ).mp (hΔφ.realize_sentence N)

/-- The second compactness step produces one finite quantifier-free disjunction. -/
theorem invariant_iff_qf_equivalent {T : L.Theory} {n : ℕ}
    (φ : L.Formula (Fin n)) :
    QFInvariant.{u, v, w} T φ ↔
      ∃ ψ : L.Formula (Fin n), ψ.IsQF ∧ T ⊨ᵇ (φ.iff ψ) := by
  classical
  constructor
  · intro hφ
    let lhom := L.lhomWithConstants (Fin n)
    let I : Set (L.Formula (Fin n)) := {δ | δ.IsQF ∧ T ⊨ᵇ δ.imp φ}
    let G : L[[Fin n]].Theory :=
      {γ | ∃ δ ∈ I, γ = Formula.equivSentence δ.not}
    let U : L[[Fin n]].Theory := lhom.onTheory T ∪ G
    have hUφ : U ⊨ᵇ Formula.equivSentence φ.not := by
      apply Theory.models_sentence_iff.mpr
      intro A
      let : L.Structure A := lhom.reduct A
      have : lhom.IsExpansionOn A := LHom.isExpansionOn_reduct _ _
      have hAT : A ⊨ T :=
        (LHom.onTheory_model lhom T).mp (A.is_model.mono Set.subset_union_left)
      let : A ⊨ T := hAT
      let M : Theory.ModelType.{u, v, max u v w} T := (Theory.ModelType.of T A).ulift
      let e : A ≃[L] M := (Equiv.ulift.symm : A ≃ M).inducedStructureEquiv
      let b : Fin n → A := fun i => (L.con i : A)
      apply (Formula.realize_equivSentence A φ.not).mpr
      apply Formula.realize_not.mpr
      intro hb
      have ha : φ.Realize (e ∘ b) := (e.toElementaryEmbedding.map_formula φ b).mpr hb
      obtain ⟨s, _, hqf, hs, himp⟩ := finite_qf_neighborhood hφ M (e ∘ b) ha
      let δ := finiteConjunction s
      have hδI : δ ∈ I := ⟨hqf, himp⟩
      have hneg := A.is_model.realize_of_mem _ (Or.inr ⟨δ, hδI, rfl⟩ :
        Formula.equivSentence δ.not ∈ U)
      have hδfalse : ¬ δ.Realize b :=
        Formula.realize_not.mp ((Formula.realize_equivSentence A δ.not).mp hneg)
      exact hδfalse ((e.toElementaryEmbedding.map_formula δ b).mp hs)
    obtain ⟨Δ, hΔ, hΔφ⟩ := Theory.models_iff_finset_models.mp hUφ
    let B := Δ.filter (· ∈ G)
    have hbδ (γ : {γ // γ ∈ B}) :
        ∃ δ ∈ I, γ.val = Formula.equivSentence δ.not :=
      (Finset.mem_filter.mp γ.property).2
    let chooseδ (γ : {γ // γ ∈ B}) : L.Formula (Fin n) := Classical.choose (hbδ γ)
    have hchoose (γ : {γ // γ ∈ B}) := Classical.choose_spec (hbδ γ)
    let s : List (L.Formula (Fin n)) := B.attach.toList.map chooseδ
    have hs (δ : L.Formula (Fin n)) (hδ : δ ∈ s) : δ ∈ I := by
      obtain ⟨γ, _, rfl⟩ := List.mem_map.mp hδ
      exact (hchoose γ).1
    refine ⟨finiteDisjunction s, finiteDisjunction_isQF s (fun δ hδ => (hs δ hδ).1), ?_⟩
    apply Theory.models_formula_iff.mpr
    intro N a
    rw [Formula.realize_iff]
    constructor
    · intro ha
      by_contra hn
      have hnot (δ : L.Formula (Fin n)) (hδ : δ ∈ s) : ¬δ.Realize a := by
        intro hh
        exact hn ((BoundedFormula.realize_foldr_sup s a default).mpr ⟨δ, hδ, hh⟩)
      let : (constantsOn (Fin n)).Structure N := constantsOn.structure a
      let : L[[Fin n]].Structure N := inferInstance
      have : lhom.IsExpansionOn N := L.withConstants_expansion _
      have hmodel : N ⊨ (↑Δ : L[[Fin n]].Theory) := by
        constructor
        intro γ hγ
        rcases hΔ hγ with hγT | hγG
        · obtain ⟨δ, hδ, rfl⟩ := hγT
          apply (LHom.realize_onSentence N lhom δ).mpr
          exact N.is_model.realize_of_mem δ hδ
        · have hγB : γ ∈ B := Finset.mem_filter.mpr ⟨hγ, hγG⟩
          let γB : {γ // γ ∈ B} := ⟨γ, hγB⟩
          have hmem : chooseδ γB ∈ s := List.mem_map.mpr ⟨γB, by simp, rfl⟩
          change N ⊨ γB.val
          rw [(hchoose γB).2]
          exact (Formula.realize_equivSentence N _).mpr (Formula.realize_not.mpr (hnot _ hmem))
      let : N ⊨ (↑Δ : L[[Fin n]].Theory) := hmodel
      have hneg := (Formula.realize_equivSentence N φ.not).mp (hΔφ.realize_sentence N)
      exact Formula.realize_not.mp hneg ha
    · intro ha
      obtain ⟨δ, hδ, hh⟩ := (BoundedFormula.realize_foldr_sup s a default).mp ha
      exact (Formula.realize_imp.mp ((hs δ hδ).2.realize_formula N (v := a))) hh
  · rintro ⟨ψ, hψ, heq⟩ M N a b hab
    have hM := Formula.realize_iff.mp (heq.realize_formula M (v := a))
    have hN := Formula.realize_iff.mp (heq.realize_formula N (v := b))
    exact hM.trans ((hab ψ hψ).trans hN.symm)


/-- Move a finite scoped context back to the same finite free context. -/
def freeFormula {n : ℕ} (φ : L.BoundedFormula Empty n) : L.Formula (Fin n) :=
  φ.toFormula.relabel (Sum.elim Empty.elim id)

private theorem toFormula_isQF {α : Type w} {n : ℕ}
    {φ : L.BoundedFormula α n} (hφ : φ.IsQF) : φ.toFormula.IsQF := by
  induction hφ with
  | falsum => exact BoundedFormula.isQF_bot
  | of_isAtomic h =>
    cases h with
    | equal t s => exact (BoundedFormula.IsAtomic.equal _ _).isQF
    | rel r ts => exact (BoundedFormula.IsAtomic.rel _ _).isQF
  | imp _ _ ihφ ihψ => exact ihφ.imp ihψ

private theorem freeFormula_isQF {n : ℕ} {φ : L.BoundedFormula Empty n}
    (hφ : φ.IsQF) : (freeFormula φ).IsQF := by
  exact (toFormula_isQF hφ).relabel _

private theorem freeFormula_realize {n : ℕ} (φ : L.BoundedFormula Empty n)
    {M : Type w} [L.Structure M] (a : Fin n → M) :
    (freeFormula φ).Realize a ↔ φ.Realize Empty.elim a := by
  rw [freeFormula, Formula.realize_relabel, BoundedFormula.realize_toFormula]
  have he : (a ∘ Sum.elim Empty.elim id) ∘ Sum.inl = (Empty.elim : Empty → M) :=
    Subsingleton.elim _ _
  have hi : (a ∘ Sum.elim Empty.elim id) ∘ Sum.inr = a := rfl
  rw [he, hi]

private theorem pack_isQF {n : ℕ} {φ : L.Formula (Fin n)} (hφ : φ.IsQF) :
    (Shared.pack φ).IsQF := by
  exact hφ.relabel Sum.inr

/-- Explicit syntax bridge to the existing bounded-context QE definition. -/
private theorem hasQE_iff_freeFormulas (T : L.Theory) :
    HasQuantifierElimination T ↔
      ∀ (n : ℕ) (φ : L.Formula (Fin n)),
        ∃ ψ : L.Formula (Fin n), ψ.IsQF ∧ T ⊨ᵇ (φ.iff ψ) := by
  constructor
  · intro h n φ
    obtain ⟨ψ, hψ, he⟩ := h n (Shared.pack φ)
    refine ⟨freeFormula ψ, freeFormula_isQF hψ, ?_⟩
    apply Theory.models_formula_iff.mpr
    intro M a
    rw [Formula.realize_iff, freeFormula_realize]
    exact (Shared.pack_realize φ a).symm.trans he.realize_bd_iff
  · intro h n φ
    obtain ⟨ψ, hψ, he⟩ := h n (freeFormula φ)
    refine ⟨Shared.pack ψ, pack_isQF hψ, ?_⟩
    intro M v a
    have hv : v = Empty.elim := Subsingleton.elim _ _
    subst v
    rw [BoundedFormula.realize_iff, Shared.pack_realize]
    exact (freeFormula_realize φ a).symm.trans
      (Formula.realize_iff.mp (he.realize_formula M))

/-- Every finite context is included, in particular the context of sentences. -/
theorem hasQE_iff_semantic (T : L.Theory) :
    HasQuantifierElimination T ↔
      ∀ (n : ℕ) (M N : Theory.ModelType.{u, v, max u v w} T)
        (a : Fin n → M) (b : Fin n → N), QFAgree (L := L) a b → FullAgree (L := L) a b := by
  rw [hasQE_iff_freeFormulas]
  constructor
  · intro h n M N a b hab φ
    exact (invariant_iff_qf_equivalent φ).mpr (h n φ) M N a b hab
  · intro h n φ
    apply (invariant_iff_qf_equivalent φ).mp
    intro M N a b hab
    exact h n M N a b hab φ

/-- Equality-only empty tuples agree on all quantifier-free sentences, at every size. -/
theorem empty_language_qf_agreement {M : Type w} {N : Type w'}
    [Language.empty.Structure M] [Language.empty.Structure N] :
    QFAgree (L := Language.empty) (Fin.elim0 : Fin 0 → M) (Fin.elim0 : Fin 0 → N) := by
  intro θ hθ
  have hs : Similar (o := false) (noRelation (M := M)) (noRelation (M := N))
      (Fin.elim0 : Fin 0 → M) (Fin.elim0 : Fin 0 → N) := by
    rintro (⟨i, _⟩ | ⟨_, i, _⟩) <;> exact Fin.elim0 i
  have he := Shared.qf_transport (o := false) (pack_isQF hθ) hs
  exact (Shared.pack_realize θ Fin.elim0).symm.trans
    (he.trans (Shared.pack_realize θ Fin.elim0))

/-- The actual sentence asserting the existence of two distinct elements. -/
def twoDistinct : Language.empty.Sentence :=
  (BoundedFormula.equal (.var (.inr (0 : Fin 2))) (.var (.inr (1 : Fin 2)))).not.ex.ex

theorem twoDistinct_realize {M : Type w} [Language.empty.Structure M] :
    M ⊨ twoDistinct ↔ ∃ x y : M, x ≠ y := by
  simp [twoDistinct, Sentence.Realize, FirstOrder.Language.Formula.Realize,
    BoundedFormula.realize_ex,
    BoundedFormula.Realize, Term.realize, Fin.snoc]

theorem one_two_element_difference :
    let : Language.empty.Structure (Fin 1) := Language.emptyStructure
    let : Language.empty.Structure (Fin 2) := Language.emptyStructure
    ¬ (Fin 1) ⊨ twoDistinct ∧ (Fin 2) ⊨ twoDistinct := by
  let : Language.empty.Structure (Fin 1) := Language.emptyStructure
  let : Language.empty.Structure (Fin 2) := Language.emptyStructure
  dsimp only
  rw [twoDistinct_realize, twoDistinct_realize]
  constructor
  · rintro ⟨x, y, hxy⟩
    exact hxy (Subsingleton.elim _ _)
  · exact ⟨0, 1, by decide⟩

theorem empty_theory_not_qe :
    ¬ HasQuantifierElimination (∅ : Language.empty.Theory) := by
  intro h
  let : Language.empty.Structure (Fin 1) := Language.emptyStructure
  let : Language.empty.Structure (Fin 2) := Language.emptyStructure
  obtain ⟨ψ, hψ, he⟩ := h 0 twoDistinct
  have hs : Similar (o := false) (noRelation (M := Fin 1)) (noRelation (M := Fin 2))
      (Fin.elim0 : Fin 0 → Fin 1) (Fin.elim0 : Fin 0 → Fin 2) := by
    rintro (⟨i, _⟩ | ⟨_, i, _⟩) <;> exact Fin.elim0 i
  have hagree : ((Fin 1) ⊨ ψ) ↔ ((Fin 2) ⊨ ψ) := by
    simpa only [Sentence.Realize, FirstOrder.Language.Formula.Realize,
      Unique.eq_default] using Shared.qf_transport (o := false) hψ hs
  have hsame : ((Fin 1) ⊨ twoDistinct) ↔ ((Fin 2) ⊨ twoDistinct) :=
    (he.models_sentence_iff (M := Fin 1)).trans
      (hagree.trans (he.models_sentence_iff (M := Fin 2)).symm)
  exact one_two_element_difference.1 (hsame.mpr one_two_element_difference.2)

end Lemmatheca.ModelTheory.QuantifierElimination.Semantic
