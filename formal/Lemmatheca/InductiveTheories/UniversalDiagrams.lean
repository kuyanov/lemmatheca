import Lemmatheca.InductiveTheories.Unions

/-! Universal named diagrams characterize the supplied existential-reflecting maps. -/
namespace Lemmatheca.ModelTheory.InductiveTheories
open FirstOrder FirstOrder.Language
open Lemmatheca.ModelTheory Lemmatheca.ModelTheory.ModelCompleteness
open Lemmatheca.ModelTheory.Theories
universe u v w w' z
variable {L : Language.{u, v}}

private theorem existential_relabel {α β : Type*} {m k : ℕ}
    {φ : L.BoundedFormula α k} (h : φ.IsExistential) (f : α → β ⊕ Fin m) :
    (φ.relabel f).IsExistential := by
  induction h with
  | of_isQF h => exact (h.relabel f).isExistential
  | ex _ ih => simpa only [BoundedFormula.relabel_ex] using ih.ex

private theorem universal_relabel {α β : Type*} {m k : ℕ}
    {φ : L.BoundedFormula α k} (h : φ.IsUniversal) (f : α → β ⊕ Fin m) :
    (φ.relabel f).IsUniversal := by
  induction h with
  | of_isQF h => exact (h.relabel f).isUniversal
  | all _ ih => simpa only [BoundedFormula.relabel_all] using ih.all

private theorem qf_restrict {α β : Type*} [DecidableEq α] {k : ℕ}
    {φ : L.BoundedFormula α k} (h : φ.IsQF) :
    ∀ f : φ.freeVarFinset → β, (φ.restrictFreeVar f).IsQF := by
  induction h with
  | falsum => exact fun _ => .falsum
  | of_isAtomic h =>
    cases h with
    | equal => exact fun _ => (BoundedFormula.IsAtomic.equal _ _).isQF
    | rel => exact fun _ => (BoundedFormula.IsAtomic.rel _ _).isQF
  | imp _ _ ih ih' => exact fun _ => (ih _).imp (ih' _)

private theorem universal_restrict {α β : Type*} [DecidableEq α] {k : ℕ}
    {φ : L.BoundedFormula α k} (h : φ.IsUniversal) :
    ∀ f : φ.freeVarFinset → β, (φ.restrictFreeVar f).IsUniversal := by
  induction h with
  | of_isQF hq => exact fun f => (qf_restrict hq f).isUniversal
  | all _ ih => exact fun f => (ih f).all

private abbrev unname {α : Type*} {n : ℕ} (φ : L[[α]].BoundedFormula Empty n) :
    L.BoundedFormula α n :=
  BoundedFormula.relabelEquiv (Equiv.sumEmpty α Empty) (BoundedFormula.constantsVarsEquiv φ)

private abbrev nameFormula {α : Type*} {n : ℕ} (φ : L.BoundedFormula α n) :
    L[[α]].BoundedFormula Empty n :=
  BoundedFormula.constantsVarsEquiv.symm
    ((BoundedFormula.relabelEquiv (Equiv.sumEmpty α Empty)).symm φ)

private theorem unnamed_qf {α : Type*} {n : ℕ} {φ : L[[α]].BoundedFormula Empty n}
    (h : φ.IsQF) : (unname φ).IsQF := by
  induction h with
  | falsum => exact .falsum
  | of_isAtomic h =>
    cases h with
    | equal => exact (BoundedFormula.IsAtomic.equal _ _).isQF
    | rel => exact (BoundedFormula.IsAtomic.rel _ _).isQF
  | imp _ _ ih ih' => exact ih.imp ih'

private theorem named_qf {α : Type*} {n : ℕ} {φ : L.BoundedFormula α n}
    (h : φ.IsQF) : (nameFormula φ).IsQF := by
  induction h with
  | falsum => exact .falsum
  | of_isAtomic h =>
    cases h with
    | equal => exact (BoundedFormula.IsAtomic.equal _ _).isQF
    | rel => exact (BoundedFormula.IsAtomic.rel _ _).isQF
  | imp _ _ ih ih' => exact ih.imp ih'

private theorem unnamed_universal {α : Type*} {n : ℕ}
    {φ : L[[α]].BoundedFormula Empty n} (h : φ.IsUniversal) : (unname φ).IsUniversal := by
  induction h with
  | of_isQF hq => exact (unnamed_qf hq).isUniversal
  | all _ ih => exact ih.all

private theorem named_universal {α : Type*} {n : ℕ}
    {φ : L.BoundedFormula α n} (h : φ.IsUniversal) : (nameFormula φ).IsUniversal := by
  induction h with
  | of_isQF hq => exact (named_qf hq).isUniversal
  | all _ ih => exact ih.all

private theorem dual_existential {α : Type z} {n : ℕ} {φ : L.BoundedFormula α n}
    (h : φ.IsExistential) : ∃ ψ : L.BoundedFormula α n, ψ.IsUniversal ∧ (∅ : L.Theory) ⊨ᵇ ψ.iff φ.not := by
  obtain ⟨ψ, hu, he⟩ := Preservation.exists_universal_not.{u,v,max u v z,z} h
  refine ⟨ψ, hu, ?_⟩
  intro B a xs
  simpa only [BoundedFormula.realize_iff, BoundedFormula.realize_not] using he B a xs

private theorem dual_universal {α : Type z} {n : ℕ} {φ : L.BoundedFormula α n}
    (h : φ.IsUniversal) : ∃ ψ : L.BoundedFormula α n, ψ.IsExistential ∧ (∅ : L.Theory) ⊨ᵇ ψ.iff φ.not := by
  obtain ⟨ψ, he, hr⟩ := Preservation.exists_existential_not.{u,v,max u v z,z} h
  refine ⟨ψ, he, ?_⟩
  intro B a xs
  simpa only [BoundedFormula.realize_iff, BoundedFormula.realize_not] using hr B a xs

private theorem reflection_finite {M : Type w} {N : Type w'} [L.Structure M]
    [L.Structure N] {f : M ↪[L] N} (hf : ExistentiallyClosedEmbedding f)
    {α : Type*} [Finite α] (φ : L.Formula α) (hφ : φ.IsExistential) (a : α → M)
    (h : φ.Realize (f ∘ a)) : φ.Realize a := by
  classical
  let : Fintype α := Fintype.ofFinite α
  let e := Fintype.equivFin α
  have hh := hf _ (φ.relabel e) (existential_relabel hφ (Sum.inl ∘ e)) (a ∘ e.symm)
  simp only [Formula.realize_relabel, Function.comp_assoc, e.symm_comp_self,
    Function.comp_id] at hh
  exact hh h

private theorem restricted_named_realize {M : Type w} [L.Structure M] [DecidableEq M]
    (γ : L[[M]].Sentence) {N : Type w'} [L.Structure N] [L[[M]].Structure N]
    [(L.lhomWithConstants M).IsExpansionOn N] :
    Formula.Realize ((Formula.equivSentence.symm γ).restrictFreeVar id)
      (fun a => Diagrams.canonicalMap L M N a.val) ↔ N ⊨ γ := by
  have h := BoundedFormula.realize_restrictFreeVar
    (φ := Formula.equivSentence.symm γ) (f := id)
    (v := fun a => Diagrams.canonicalMap L M N a.val) (xs := (default : Fin 0 → N))
    (Diagrams.canonicalMap L M N) (fun _ => rfl)
  exact h.trans (Formula.realize_equivSentence_symm_con N γ)

/-- Canonical interpretations of names recover the original map and existential reflection. -/
theorem universalDiagram_iff_reflection (M : Type w) [L.Structure M] [Nonempty M]
    (N : Type w') [L.Structure N] [Nonempty N] [L[[M]].Structure N]
    [(L.lhomWithConstants M).IsExpansionOn N] :
    N ⊨ universalDiagram L M ↔
      ∃ f : M ↪[L] N, (f : M → N) = Diagrams.canonicalMap L M N ∧
        ExistentiallyClosedEmbedding f := by
  classical
  constructor
  · intro hN
    obtain ⟨f, hcanon⟩ := Diagrams.model_signed_iff_canonical_embedding.mp
      (hN.mono (signedDiagram_subset_universalDiagram M))
    refine ⟨f, hcanon, ?_⟩
    intro n φ hφ a hNa
    by_contra hMa
    obtain ⟨ψ, hψ, he⟩ := dual_existential hφ
    have hMψ : Formula.Realize ψ a :=
      (Formula.realize_iff.mp (he.realize_formula M (v := a))).mpr (Formula.realize_not.mpr hMa)
    have hσ : (Diagrams.namedFormula ψ a).IsUniversal :=
      named_universal (universal_relabel hψ (Sum.inl ∘ a))
    have hMσ : M ⊨ Diagrams.namedFormula ψ a :=
      (Diagrams.realize_namedFormula (N := M) ψ a).mpr hMψ
    have hNψ := (Diagrams.realize_namedFormula ψ a).mp
      (hN.realize_of_mem _ ⟨hσ, hMσ⟩)
    have hψa : Formula.Realize ψ (f ∘ a) := by rw [hcanon]; exact hNψ
    exact Formula.realize_not.mp ((Formula.realize_iff.mp (he.realize_formula N (v := f ∘ a))).mp hψa) hNa
  · rintro ⟨f, hcanon, hf⟩
    constructor
    rintro γ ⟨hγ, hMγ⟩
    let ψ : L.Formula M := Formula.equivSentence.symm γ
    let φ : L.Formula ψ.freeVarFinset := ψ.restrictFreeVar id
    have hφ : φ.IsUniversal := universal_restrict (unnamed_universal hγ) id
    obtain ⟨ξ, hξ, he⟩ := dual_universal hφ
    have hMφ : φ.Realize (Subtype.val : ψ.freeVarFinset → M) :=
      (restricted_named_realize γ (N := M)).mpr hMγ
    by_contra hNγ
    have hNφ : ¬ φ.Realize (f ∘ (Subtype.val : ψ.freeVarFinset → M)) := by
      rw [hcanon]
      exact fun h => hNγ ((restricted_named_realize γ).mp h)
    have hNξ : Formula.Realize ξ (f ∘ (Subtype.val : ψ.freeVarFinset → M)) :=
      (Formula.realize_iff.mp (he.realize_formula N (v := f ∘ (Subtype.val : ψ.freeVarFinset → M)))).mpr (Formula.realize_not.mpr hNφ)
    have hMξ := reflection_finite hf ξ hξ Subtype.val hNξ
    exact Formula.realize_not.mp ((Formula.realize_iff.mp (he.realize_formula M (v := (Subtype.val : ψ.freeVarFinset → M)))).mp hMξ) hMφ

private theorem universal_binary (φ ψ : L.Sentence) (hφ : φ.IsUniversal)
    (hψ : ψ.IsUniversal) :
    ∃ χ : L.Sentence, χ.IsUniversal ∧ (∅ : L.Theory) ⊨ᵇ χ.iff (φ ⊓ ψ) := by
  obtain ⟨φ', hφ', heφ⟩ := dual_universal hφ
  obtain ⟨ψ', hψ', heψ⟩ := dual_universal hψ
  obtain ⟨η, hη, hrη⟩ := Preservation.exists_existential_binary.{u,v,max u v,0} hφ' hψ' false
  obtain ⟨χ, hχ, hrχ⟩ := dual_existential hη
  refine ⟨χ, hχ, ?_⟩
  intro B a xs
  have hp := BoundedFormula.realize_iff.mp (heφ B a xs)
  have hq := BoundedFormula.realize_iff.mp (heψ B a xs)
  have hn := BoundedFormula.realize_iff.mp (hrχ B a xs)
  have hc := hrη B a xs
  simp only [Bool.false_eq_true, ite_false] at hc
  simp only [BoundedFormula.realize_not] at hp hq hn
  rw [BoundedFormula.realize_iff, BoundedFormula.realize_inf]
  tauto

private theorem universal_fold (s : List L.Sentence) (h : ∀ φ ∈ s, φ.IsUniversal) :
    ∃ χ : L.Sentence, χ.IsUniversal ∧ (∅ : L.Theory) ⊨ᵇ χ.iff (s.foldr (· ⊓ ·) ⊤) := by
  induction s with
  | nil =>
    refine ⟨⊤, BoundedFormula.IsQF.top.isUniversal, ?_⟩
    intro B a xs
    simp
  | cons φ s ih =>
    obtain ⟨ψ, hψ, heψ⟩ := ih (fun θ hθ => h θ (by simp [hθ]))
    obtain ⟨χ, hχ, heχ⟩ := universal_binary φ ψ (h φ (by simp)) hψ
    refine ⟨χ, hχ, ?_⟩
    intro B a xs
    have hp := BoundedFormula.realize_iff.mp (heψ B a xs)
    have hc := BoundedFormula.realize_iff.mp (heχ B a xs)
    simpa only [List.foldr_cons, BoundedFormula.realize_iff, BoundedFormula.realize_inf, hp] using hc

private theorem prefix_alls {α : Type*} {n : ℕ} {φ : L.BoundedFormula α n}
    (h : IsUniversalExistential φ) : IsUniversalExistential φ.alls := by
  induction n with
  | zero => exact h
  | succ n ih => exact ih h.all

private noncomputable def closeExistential {α : Type*} [Finite α] (φ : L.Formula α) :
    L.Sentence := (Formula.relabel Sum.inr φ).iAlls α

private theorem closeExistential_prefix {α : Type*} [Finite α] {φ : L.Formula α}
    (hφ : φ.IsExistential) : IsUniversalExistential (closeExistential φ) := by
  unfold closeExistential Formula.iAlls
  apply prefix_alls
  exact .of_existential (existential_relabel (existential_relabel hφ (Sum.inl ∘ Sum.inr)) _)

private theorem closeExistential_realize {α : Type*} [Finite α] (φ : L.Formula α)
    {M : Type w} [L.Structure M] :
    M ⊨ closeExistential φ ↔ ∀ a : α → M, φ.Realize a := by
  simp only [closeExistential, Sentence.Realize, Formula.realize_iAlls,
    Formula.realize_relabel, Sum.elim_comp_inr]

/-- The particular universal-diagram theory is satisfiable under the actual consequences. -/
theorem universalDiagram_satisfiable (T : L.Theory) (M : Type w)
    [L.Structure M] [Nonempty M] (hM : M ⊨ universalExistentialPart T) :
    ((L.lhomWithConstants M).onTheory T ∪ universalDiagram L M).IsSatisfiable := by
  classical
  apply Theory.isSatisfiable_iff_isFinitelySatisfiable.mpr
  intro Γ hΓ
  by_contra hno
  let Δ := Γ.filter (fun γ => γ ∈ universalDiagram L M)
  obtain ⟨γ, hγ, heγ⟩ := universal_fold Δ.toList
    (fun δ hδ => (Finset.mem_filter.mp (Finset.mem_toList.mp hδ)).2.1)
  have hMΔ : M ⊨ finiteConjunction Δ := (realize_finiteConjunction Δ M).mpr
    ⟨fun δ hδ => (Finset.mem_filter.mp hδ).2.2⟩
  have hMγ : M ⊨ γ := (Formula.realize_iff.mp (heγ.realize_sentence M)).mpr hMΔ
  let ψ : L.Formula M := Formula.equivSentence.symm γ
  let φ : L.Formula ψ.freeVarFinset := ψ.restrictFreeVar id
  have hφ : φ.IsUniversal := universal_restrict (unnamed_universal hγ) id
  obtain ⟨ξ, hξ, heξ⟩ := dual_universal hφ
  let σ : L.Sentence := closeExistential ξ
  have hTσ : T ⊨ᵇ σ := by
    apply Theory.models_sentence_iff.mpr
    intro B
    apply (closeExistential_realize ξ).mpr
    intro a
    by_contra hξa
    have hφa : φ.Realize a := by
      by_contra hnot
      exact hξa ((Formula.realize_iff.mp (heξ.realize_formula B (v := a))).mpr
        (Formula.realize_not.mpr hnot))
    have hex : B ⊨ ψ.exClosure := (Formula.realize_exClosure ψ).mpr ⟨a, hφa⟩
    obtain ⟨f, hf⟩ := Formula.exists_realize_equivSentence_iff_realize_exClosure.mpr hex
    let : L[[M]].Structure B := Diagrams.namedExpansion (L := L) f
    let : (L.lhomWithConstants M).IsExpansionOn B := Diagrams.namedExpansion_isExpansion f
    have hBγ : B ⊨ γ := by simpa only [ψ, Equiv.apply_symm_apply] using hf
    have hBΔ : B ⊨ (↑Δ : L[[M]].Theory) := (realize_finiteConjunction Δ B).mp
      ((Formula.realize_iff.mp (heγ.realize_sentence B)).mp hBγ)
    let : B ⊨ (↑Γ : L[[M]].Theory) := by
      constructor
      intro δ hδ
      rcases hΓ hδ with hT | hD
      · obtain ⟨θ, hθ, rfl⟩ := hT
        exact (LHom.realize_onSentence B _ θ).mpr (B.is_model.realize_of_mem θ hθ)
      · exact hBΔ.realize_of_mem δ (Finset.mem_filter.mpr ⟨hδ, hD⟩)
    exact hno (Theory.Model.isSatisfiable B)
  have hMσ : M ⊨ σ := hM.realize_of_mem σ ⟨closeExistential_prefix hξ, hTσ⟩
  have hexM : M ⊨ ψ.exClosure := Formula.realize_exClosure_of_realize_equivSentence
    (by simpa only [ψ, Equiv.apply_symm_apply] using hMγ)
  obtain ⟨a, ha⟩ := (Formula.realize_exClosure ψ).mp hexM
  have hMξ := (closeExistential_realize ξ).mp hMσ a
  exact Formula.realize_not.mp
    ((Formula.realize_iff.mp (heξ.realize_formula M (v := a))).mp hMξ) ha

private theorem qf_toFormula {α : Type*} {k : ℕ} {φ : L.BoundedFormula α k}
    (h : φ.IsQF) : φ.toFormula.IsQF := by
  induction h with
  | falsum => exact BoundedFormula.isQF_bot
  | of_isAtomic h =>
    cases h with
    | equal t s => exact (BoundedFormula.IsAtomic.equal _ _).isQF
    | rel R ts => exact (BoundedFormula.IsAtomic.rel _ _).isQF
  | imp _ _ ihφ ihψ => exact ihφ.imp ihψ

private theorem existential_toFormula {α : Type*} {k : ℕ}
    {φ : L.BoundedFormula α k} (h : φ.IsExistential) : φ.toFormula.IsExistential := by
  induction h with
  | of_isQF h => exact (qf_toFormula h).isExistential
  | ex _ ih =>
    exact (existential_relabel ih _).ex

/-- The existing scoped variables become the finite free-variable context. -/
private def unpack {k : ℕ} (φ : L.BoundedFormula Empty k) : L.Formula (Fin k) :=
  φ.toFormula.relabel (Sum.elim Empty.elim id)

private theorem unpack_realize {M : Type*} [L.Structure M] {k : ℕ}
    (φ : L.BoundedFormula Empty k) (a : Fin k → M) :
    (unpack φ).Realize a ↔ φ.Realize default a := by
  rw [unpack, Formula.realize_relabel, BoundedFormula.realize_toFormula]
  have hv : (a ∘ Sum.elim Empty.elim id) ∘ Sum.inl = (default : Empty → M) :=
    Subsingleton.elim _ _
  rw [hv]
  rfl

private theorem unpack_existential {k : ℕ} {φ : L.BoundedFormula Empty k}
    (h : φ.IsExistential) : (unpack φ).IsExistential :=
  existential_relabel (existential_toFormula h) _

/-- The consequence test produces a model and an existential-reflecting embedding into it. -/
theorem model_part_iff_reflecting_embedding (T : L.Theory) (M : Type w)
    [L.Structure M] [Nonempty M] :
    M ⊨ universalExistentialPart T ↔
      ∃ (N : Type (max u v w)) (_ : L.Structure N) (_ : Nonempty N)
        (_ : N ⊨ T) (f : M ↪[L] N), ExistentiallyClosedEmbedding f := by
  classical
  constructor
  · intro hM
    let hsat := universalDiagram_satisfiable T M hM
    let N := hsat.some
    let : L.Structure N := (L.lhomWithConstants M).reduct N
    let : (L.lhomWithConstants M).IsExpansionOn N := LHom.isExpansionOn_reduct _ _
    have hNT : N ⊨ T := (LHom.onTheory_model _ _).mp
      (N.is_model.mono Set.subset_union_left)
    have hND : N ⊨ universalDiagram L M := N.is_model.mono Set.subset_union_right
    obtain ⟨f, _, hf⟩ := (universalDiagram_iff_reflection M N).mp hND
    exact ⟨N, inferInstance, inferInstance, hNT, f, hf⟩
  · rintro ⟨N, SN, hne, hNT, f, hf⟩
    let := SN
    let := hne
    let := hNT
    constructor
    intro σ hσ
    have hNσ : N ⊨ σ := hσ.2.realize_sentence N
    have reflect_prefix {n : ℕ} {φ : L.BoundedFormula Empty n}
        (hp : IsUniversalExistential φ) (a : Fin n → M)
        (ha : φ.Realize default (f ∘ a)) : φ.Realize default a := by
      induction hp with
      | @of_existential m ψ he =>
        have hNφ : (unpack ψ).Realize (f ∘ a) := (unpack_realize ψ _).mpr ha
        exact (unpack_realize ψ a).mp (hf _ (unpack ψ) (unpack_existential he) a hNφ)
      | @all m ψ hp ih =>
        rw [BoundedFormula.realize_all] at ha ⊢
        intro b
        have heq : f ∘ Fin.snoc a b = Fin.snoc (f ∘ a) (f b) := by
          funext i
          refine Fin.lastCases ?_ (fun i => ?_) i
          · simp only [Function.comp_apply, Fin.snoc_last]
          · simp only [Function.comp_apply, Fin.snoc_castSucc]
        exact ih _ (heq.symm ▸ ha (f b))
    exact reflect_prefix hσ.1 default (by
      have heq : f ∘ (default : Fin 0 → M) = (default : Fin 0 → N) := Subsingleton.elim _ _
      rw [heq]
      exact hNσ)

private theorem elementary_from_cofinal_sequence
    (G : ℕ → Type (max u v w)) [∀ n, L.Structure (G n)] [∀ n, Nonempty (G n)]
    {C : Type (max u v w)} [L.Structure C]
    (j : ∀ n, G n ↪[L] C) (step : ∀ n, G n ↪ₑ[L] G (n + 1))
    (comm : ∀ n a, j (n + 1) (step n a) = j n a)
    (cover : ∀ x : C, ∃ n a, j n a = x) :
    ∀ n, ∃ e : G n ↪ₑ[L] C, (e : G n → C) = j n := by
  classical
  let R : ℕ → L.Substructure C := fun n => (j n).toHom.range
  have hR : Monotone R := by
    apply monotone_nat_of_le_succ
    intro n x hx
    obtain ⟨a, rfl⟩ := hx
    exact ⟨step n a, comm n a⟩
  let S : ElementaryChains.IncreasingChain L C :=
    { stage := ⟨R, hR⟩
      nonempty_stage := fun n => by
        obtain ⟨a⟩ := (inferInstance : Nonempty (G n))
        exact ⟨j n a, a, rfl⟩ }
  have hS : S.IsElementary := by
    apply (S.isElementary_iff_successor).mpr
    intro n
    let g : S.stage n ↪ₑ[L] S.stage (n + 1) :=
      (j (n + 1)).equivRange.toElementaryEmbedding.comp
        ((step n).comp (j n).equivRange.symm.toElementaryEmbedding)
    refine ⟨g, ?_⟩
    funext x
    apply Subtype.ext
    change j (n + 1) (step n ((j n).equivRange.symm x)) = (x : C)
    rw [comm]
    exact congrArg Subtype.val ((j n).equivRange.apply_symm_apply x)
  have htop : S.unionSubstructure = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨n, a, rfl⟩ := cover x
    exact le_iSup S.stage n ⟨a, rfl⟩
  have hsurj : Function.Surjective S.unionSubstructure.subtype := by
    intro x
    exact ⟨⟨x, by rw [htop]; trivial⟩, rfl⟩
  let E : S.unionSubstructure ≃[L] C :=
    { toEquiv := Equiv.ofBijective S.unionSubstructure.subtype
        ⟨S.unionSubstructure.subtype.injective, hsurj⟩
      map_fun' := S.unionSubstructure.subtype.map_fun'
      map_rel' := S.unionSubstructure.subtype.map_rel' }
  intro n
  obtain ⟨e, he⟩ := S.elementary_union hS n
  refine ⟨E.toElementaryEmbedding.comp
    (e.comp (j n).equivRange.toElementaryEmbedding), ?_⟩
  funext a
  change (e ((j n).equivRange a) : C) = j n a
  rw [he]
  rfl


end Lemmatheca.ModelTheory.InductiveTheories
