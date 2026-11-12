import Lemmatheca.StronglyMinimalTypes.Bounds
import Lemmatheca.CountableSaturatedModels.Constructions

/-! Finite tuple type counts from the existing one-variable stability convention.
The prefix realization is chosen in a small actual model. Its tail conditions
are translated into the native parameter language naming that whole model.
-/
namespace Lemmatheca.ModelTheory.StronglyMinimalTypes
open FirstOrder FirstOrder.Language FirstOrder.Language.Structure Cardinal
open Lemmatheca.ModelTheory
open Types OrderPatternsAndStability
universe u
noncomputable section
variable {L : Language.{u,u}} {T : L.Theory} {n : ℕ}

/-- A chosen actual model and tuple for a native complete type. -/
def tupleModel (p : T.CompleteType (Fin n)) : T.ModelType.{u,u,u} :=
  (T.exists_modelType_is_realized_in p).choose

def realizingTuple (p : T.CompleteType (Fin n)) : Fin n → tupleModel p :=
  ((T.exists_modelType_is_realized_in p).choose_spec).choose

theorem realizingTuple_type (p : T.CompleteType (Fin n)) :
    T.typeOf (realizingTuple p) = p := by
  exact ((T.exists_modelType_is_realized_in p).choose_spec).choose_spec

/-- Restriction to the first n object variables; its formula recovery is proved below. -/
def prefixType (p : T.CompleteType (Fin (n+1))) : T.CompleteType (Fin n) :=
  T.typeOf (fun i => realizingTuple p i.castSucc)

theorem prefixType_membership (p : T.CompleteType (Fin (n+1)))
    (φ : L.Formula (Fin n)) :
    φ ∈ formulas (prefixType p) ↔ φ.relabel Fin.castSucc ∈ formulas p := by
  have h : Formula.equivSentence (φ.relabel Fin.castSucc) ∈
      T.typeOf (realizingTuple p) ↔
      (φ.relabel Fin.castSucc).Realize (realizingTuple p) :=
    Theory.CompleteType.formula_mem_typeOf
  rw [realizingTuple_type] at h
  change Formula.equivSentence φ ∈ T.typeOf
    (fun i => realizingTuple p i.castSucc) ↔ _
  rw [Theory.CompleteType.formula_mem_typeOf]
  change φ.Realize (fun i => realizingTuple p i.castSucc) ↔
    Formula.equivSentence (φ.relabel Fin.castSucc) ∈ p
  rw [h]
  simp only [Formula.realize_relabel, Function.comp_def]

variable {M : Type u} [L.Structure M] [Nonempty M]

/-- The fixed small named model realizes the actual given prefix type. -/
structure SmallPrefixRealization (A : Set M) (r : TypesOver (L := L) A n)
    (κ : Cardinal.{u}) where
  model : (L[[A]].completeTheory M).ModelType.{u,u,u}
  tuple : Fin n → model
  type_eq : (L[[A]].completeTheory M).typeOf tuple = r
  card_le : #model ≤ κ

namespace SmallPrefixRealization
variable {A : Set M} {r : TypesOver (L := L) A n} {κ : Cardinal.{u}}

/-- Forget the extra parameter symbols, retaining their specified interpretations separately. -/
abbrev reduct (R : SmallPrefixRealization A r κ) : Type u := R.model
instance (R : SmallPrefixRealization A r κ) : L.Structure R.reduct :=
  (L.lhomWithConstants A).reduct R.model
instance (R : SmallPrefixRealization A r κ) : Nonempty R.reduct := inferInstanceAs (Nonempty R.model)
instance (R : SmallPrefixRealization A r κ) : L[[A]].Structure R.reduct := R.model.struc
instance (R : SmallPrefixRealization A r κ) :
    (L.lhomWithConstants A).IsExpansionOn R.reduct := LHom.isExpansionOn_reduct _ _

def parameters (R : SmallPrefixRealization A r κ) : A → R.reduct :=
  fun a => (L.con a : R.model)
end SmallPrefixRealization

omit [Nonempty M] in
/-- Downward Löwenheim–Skolem in the original named language preserves the realizing tuple. -/
theorem exists_small_prefix (A : Set M) (r : TypesOver (L := L) A n)
    (κ : Cardinal.{u}) (hκ : ℵ₀ ≤ κ) (hL : L.card ≤ κ) (hA : #A ≤ κ) :
    Nonempty (SmallPrefixRealization A r κ) := by
  obtain ⟨N, a, ha⟩ := (L[[A]].completeTheory M).exists_modelType_is_realized_in r
  obtain ⟨S, hS, hc⟩ := ElementarySubmodels.exists_elementarySubstructure_card_le
    (L := L[[A]]) (Set.range a)
  let b : Fin n → S := fun i => ⟨a i, hS (Set.mem_range_self i)⟩
  have hb : (L[[A]].completeTheory M).typeOf b = r := by
    apply Eq.symm
    apply (realizes_complete_iff r b).mp
    intro φ hφ
    apply (S.subtype.map_formula φ b).mp
    change φ.Realize a
    exact ((realizes_complete_iff r a).mpr ha.symm) φ hφ
  refine ⟨⟨Theory.ModelType.of (L[[A]].completeTheory M) S, b, hb, hc.trans ?_⟩⟩
  apply max_le hκ
  apply max_le
  · rw [Language.card_withConstants]
    exact Cardinal.add_le_of_le hκ (by simpa only [Cardinal.lift_id] using hL) (by simpa only [Cardinal.lift_id] using hA)
  · let : Finite (Set.range a) := (Set.finite_range a).to_subtype
    exact Cardinal.mk_le_aleph0.trans hκ

/-- Substitute the fixed prefix and old parameters, leaving only the last variable. -/
def tailFormula {A : Set M} {N : Type u} (ρ : A → N) (a : Fin n → N)
    (φ : L[[A]].Formula (Fin (n+1))) : L[[(Set.univ : Set N)]].Formula (Fin 1) :=
  ((L.lhomWithConstantsMap (fun x : A =>
    (⟨ρ x, Set.mem_univ _⟩ : (Set.univ : Set N)))).onFormula φ).subst
      (Fin.lastCases (Term.var 0) (fun i =>
        Constants.term (L.con (⟨a i, Set.mem_univ _⟩ : (Set.univ : Set N)))))

omit [L.Structure M] [Nonempty M] in
/-- The exact substitution identity used in the finite-consistency proof. -/
theorem tailFormula_realize {A : Set M} {N : Type u}
    [L[[A]].Structure N] [L.Structure N] [(L.lhomWithConstants A).IsExpansionOn N]
    (a : Fin n → N) (z : N) (φ : L[[A]].Formula (Fin (n+1))) :
    (tailFormula (fun x : A => (L.con x : N)) a φ).Realize (fun _ => z) ↔
      φ.Realize (Fin.snoc a z) := by
  let f := L.lhomWithConstantsMap (fun x : A =>
    (⟨(L.con x : N), Set.mem_univ _⟩ : (Set.univ : Set N)))
  let : f.IsExpansionOn N := by
    constructor
    · intro k g xs
      cases g with
      | inl g =>
        change @funMap L N _ k g xs = @funMap L[[A]] N _ k (Sum.inl g) xs
        exact ((L.lhomWithConstants A).map_onFunction g xs).symm
      | inr c =>
        cases k with
        | zero =>
          change (L.con (α := A) c : N) = @funMap L[[A]] N _ 0 (Sum.inr c) xs
          rw [Unique.eq_default xs]
          rfl
        | succ k => exact isEmptyElim c
    · intro k g xs
      cases g with
      | inl g =>
        change @RelMap L N _ k g xs = @RelMap L[[A]] N _ k (Sum.inl g) xs
        exact ((L.lhomWithConstants A).map_onRelation g xs).symm
      | inr c => exact isEmptyElim c
  let t : Fin (n+1) → L[[(Set.univ : Set N)]].Term (Fin 1) :=
    Fin.lastCases (Term.var 0) (fun i =>
      Constants.term (L.con (⟨a i, Set.mem_univ _⟩ : (Set.univ : Set N))))
  change Formula.Realize ((f.onFormula φ).subst t) (fun _ => z) ↔ _
  simp only [Formula.Realize, BoundedFormula.realize_subst]
  change (f.onFormula φ).Realize (fun i => (t i).realize (fun _ => z)) ↔ _
  rw [LHom.realize_onFormula]
  have ht : (fun i => (t i).realize (fun _ => z)) = Fin.snoc a z := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [t]
    · simp [t]
  rw [ht]
  rfl

/-- Tail conditions retain every formula of the given original type. -/
def tailConditions {A : Set M} {r : TypesOver (L := L) A n} {κ : Cardinal.{u}}
    (R : SmallPrefixRealization A r κ) (p : TypesOver (L := L) A (n+1)) :
    Set (L[[(Set.univ : Set R.reduct)]].Formula (Fin 1)) :=
  tailFormula R.parameters (fun i => R.tuple i) '' formulas p

private def lastExists (φ : L.Formula (Fin (n+1))) : L.Formula (Fin n) :=
  (φ.relabel finSumFinEquiv.symm).iExs (Fin 1)

private theorem snoc_eta {P : Type u} (a : Fin (n+1) → P) :
    Fin.snoc (fun i => a i.castSucc) (a (Fin.last n)) = a := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp

private theorem lastExists_realize {P : Type u} [L.Structure P]
    (φ : L.Formula (Fin (n+1))) (a : Fin n → P) :
    (lastExists φ).Realize a ↔ ∃ z : P, φ.Realize (Fin.snoc a z) := by
  simp only [lastExists, Formula.realize_iExs, Formula.realize_relabel]
  have hv (b : Fin 1 → P) : Sum.elim a b ∘ finSumFinEquiv.symm = Fin.snoc a (b 0) := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨b 0, hv b ▸ hb⟩
  · rintro ⟨z, hz⟩
    exact ⟨fun _ => z, (hv (fun _ => z)).symm ▸ hz⟩

omit [Nonempty M] in
/-- Completeness of the common prefix gives witnesses in the same chosen small model. -/
theorem tailConditions_finitelyRealized {A : Set M} {r : TypesOver (L := L) A n}
    {κ : Cardinal.{u}} (R : SmallPrefixRealization A r κ)
    (p : TypesOver (L := L) A (n+1)) (hp : prefixType p = r) :
    FinitelyRealized R.reduct (tailConditions R p) := by
  classical
  intro Γ hΓ
  let origin : Γ → L[[A]].Formula (Fin (n+1)) := fun ψ => (hΓ ψ.property).choose
  have hmem (ψ : Γ) : origin ψ ∈ formulas p := (hΓ ψ.property).choose_spec.1
  have heq (ψ : Γ) : tailFormula R.parameters (fun i => R.tuple i) (origin ψ) = ψ.val :=
    (hΓ ψ.property).choose_spec.2
  let Δ := Γ.attach.image origin
  let χ : L[[A]].Formula (Fin (n+1)) := Formula.iInf (fun φ : Δ => φ.val)
  have hχ : χ.Realize (realizingTuple p) := by
    rw [Formula.realize_iInf]
    intro φ
    obtain ⟨ψ, _, hψ⟩ := Finset.mem_image.mp φ.property
    rw [← hψ]
    exact ((realizes_complete_iff p (realizingTuple p)).mpr
      (realizingTuple_type p).symm) _ (hmem ψ)
  have hprefix : lastExists χ ∈ formulas (prefixType p) := by
    apply Theory.CompleteType.formula_mem_typeOf.mpr
    apply (lastExists_realize χ _).mpr
    exact ⟨realizingTuple p (Fin.last n), (snoc_eta _).symm ▸ hχ⟩
  rw [hp] at hprefix
  have hR : (lastExists χ).Realize R.tuple := by
    have hm : Formula.equivSentence (lastExists χ) ∈
        (L[[A]].completeTheory M).typeOf R.tuple := by
      rw [R.type_eq]
      exact hprefix
    exact Theory.CompleteType.formula_mem_typeOf.mp hm
  obtain ⟨z, hz⟩ := (lastExists_realize χ R.tuple).mp hR
  refine ⟨fun _ => z, fun ψ hψ => ?_⟩
  let q : Γ := ⟨ψ, hψ⟩
  have hd : origin q ∈ Δ := Finset.mem_image.mpr ⟨q, Finset.mem_attach _ _, rfl⟩
  have hf : (origin q).Realize (Fin.snoc R.tuple z) :=
    (Formula.realize_iInf.mp hz) ⟨origin q, hd⟩
  have heq' : tailFormula R.parameters R.tuple (origin q) = ψ := heq q
  rw [← heq']
  exact (tailFormula_realize R.tuple z (origin q)).mpr hf

/-- Choose one complete extension over the entire small model. -/
def selectedTail {A : Set M} {r : TypesOver (L := L) A n} {κ : Cardinal.{u}}
    (R : SmallPrefixRealization A r κ)
    (p : {p : TypesOver (L := L) A (n+1) // prefixType p = r}) :
    TypesOver (L := L) (Set.univ : Set R.reduct) 1 :=
  (exists_complete_extension (tailConditions R p.val)
    ((partial_iff_finitelyRealized_completeTheory _).mpr
      (tailConditions_finitelyRealized R p.val p.property))).choose

omit [Nonempty M] in
/-- The same selected one-type determines every formula of the original tuple type. -/
theorem selectedTail_membership {A : Set M} {r : TypesOver (L := L) A n}
    {κ : Cardinal.{u}} (R : SmallPrefixRealization A r κ)
    (p : {p : TypesOver (L := L) A (n+1) // prefixType p = r})
    (φ : L[[A]].Formula (Fin (n+1))) :
    tailFormula R.parameters (fun i => R.tuple i) φ ∈ formulas (selectedTail R p) ↔
      φ ∈ formulas p.val := by
  classical
  have hext : tailConditions R p.val ⊆ formulas (selectedTail R p) :=
    (exists_complete_extension (tailConditions R p.val)
      ((partial_iff_finitelyRealized_completeTheory _).mpr
        (tailConditions_finitelyRealized R p.val p.property))).choose_spec
  constructor
  · intro ht
    by_contra hn
    have hnot : φ.not ∈ formulas p.val := (p.val.not_mem_iff _).mpr hn
    have htneg := hext ⟨φ.not, hnot, rfl⟩
    have he : tailFormula R.parameters R.tuple φ.not =
        (tailFormula R.parameters R.tuple φ).not := rfl
    rw [he] at htneg
    exact ((selectedTail R p).not_mem_iff _).mp htneg ht
  · intro hφ
    exact hext ⟨φ, hφ, rfl⟩

omit [Nonempty M] in
/-- Distinct extensions of a prefix have distinct selected native one-types. -/
theorem selectedTail_injective {A : Set M} {r : TypesOver (L := L) A n}
    {κ : Cardinal.{u}} (R : SmallPrefixRealization A r κ) :
    Function.Injective (selectedTail R) := by
  intro p q h
  apply Subtype.ext
  apply SetLike.ext
  intro γ
  change γ ∈ p.val.toTheory ↔ γ ∈ q.val.toTheory
  have hp := selectedTail_membership R p (Formula.equivSentence.symm γ)
  have hq := selectedTail_membership R q (Formula.equivSentence.symm γ)
  rw [h] at hp
  simpa only [formulas, Set.mem_preimage, Equiv.apply_symm_apply] using hp.symm.trans hq

omit [Nonempty M] in
/-- The whole small model is an allowed parameter set in the original stability bound. -/
theorem prefix_fiber_cardinal_bound (T : L.Theory) [M ⊨ T]
    (A : Set M) (κ : Cardinal.{u}) (hκ : ℵ₀ ≤ κ) (hL : L.card ≤ κ)
    (hA : #A ≤ κ) (hstable : KappaStable.{u,u,u} T κ)
    (r : TypesOver (L := L) A n) :
    #({p : TypesOver (L := L) A (n+1) // prefixType p = r}) ≤ κ := by
  classical
  let R := Classical.choice (exists_small_prefix A r κ hκ hL hA)
  let : R.reduct ⊨ T := by
    constructor
    intro σ hσ
    have hm : M ⊨ σ := Theory.realize_sentence_of_mem T hσ
    have hk : (L.lhomWithConstants A).onSentence σ ∈ L[[A]].completeTheory M := by
      exact (Language.mem_completeTheory).mpr ((LHom.realize_onSentence M _ _).mpr hm)
    have hn := R.model.is_model.realize_of_mem _ hk
    exact (LHom.realize_onSentence R.reduct _ _).mp hn
  let P : T.ModelType.{u,u,u} := Theory.ModelType.of T R.reduct
  have hU : #(Set.univ : Set P) ≤ κ := by
    rw [Cardinal.mk_univ]
    exact R.card_le
  exact (Cardinal.mk_le_of_injective (selectedTail_injective R)).trans
    (hstable.2 P Set.univ hU)

/-- The named theory fixes its zero-type; counting prefix fibers gives the induction. -/
theorem finite_tuple_bound (T : L.Theory) [M ⊨ T]
    (A : Set M) (κ : Cardinal.{u}) (hκ : ℵ₀ ≤ κ) (hL : L.card ≤ κ)
    (hA : #A ≤ κ) (hstable : KappaStable.{u,u,u} T κ) (r : ℕ) :
    #(TypesOver (L := L) A r) ≤ κ := by
  induction r with
  | zero =>
    let : Subsingleton (TypesOver (L := L) A 0) := ⟨zero_type_unique⟩
    exact Cardinal.mk_le_aleph0.trans hκ
  | succ n ih =>
    have hf : ∀ q : TypesOver (L := L) A n,
        #(prefixType ⁻¹' {q}) ≤ κ := by
      intro q
      exact prefix_fiber_cardinal_bound T A κ hκ hL hA hstable q
    have h := Cardinal.mk_le_mk_mul_of_mk_preimage_le prefixType hf
    exact h.trans ((mul_le_mul' ih le_rfl).trans (by simp [Cardinal.mul_eq_self hκ]))

/-- Apply the general bridge to the existing one-variable strongly minimal bound. -/
theorem stronglyMinimal_finite_tuple_bound (T : L.Theory) (hT : T.IsComplete)
    (hSM : StronglyMinimalSets.StronglyMinimalTheory T) [M ⊨ T]
    (A : Set M) (κ : Cardinal.{u}) (hκ : ℵ₀ ≤ κ) (hL : L.card ≤ κ)
    (hA : #A ≤ κ) (r : ℕ) : #(TypesOver (L := L) A r) ≤ κ := by
  apply finite_tuple_bound T A κ hκ hL hA
  exact stronglyMinimal_kappaStable T hT hSM κ hκ (by simpa using hL)

/-- A complete theory's native types embed in the empty-parameter type space of any model. -/
theorem native_types_empty_parameters_injection (T : L.Theory) (hT : T.IsComplete)
    [M ⊨ T] (r : ℕ) :
    ∃ f : T.CompleteType (Fin r) → TypesOver (L := L) (∅ : Set M) r,
      Function.Injective f := by
  classical
  let A : Set M := ∅
  let e := LEquiv.addEmptyConstants L A
  have lift (p : T.CompleteType (Fin r)) :
      ∃ q : TypesOver (L := L) A r, ∀ φ : L.Formula (Fin r),
        φ ∈ formulas p ↔ (L.lhomWithConstants A).onFormula φ ∈ formulas q := by
    obtain ⟨N, a, ha⟩ := T.exists_modelType_is_realized_in p
    let : (constantsOn A).Structure N := constantsOn.structure
      (fun x : A => False.elim x.property)
    let : L[[A]].Structure N := inferInstance
    let : (L.lhomWithConstants A).IsExpansionOn N := L.withConstants_expansion _
    let : e.toLHom.IsExpansionOn N := by
      change (L.lhomWithConstants A).IsExpansionOn N
      infer_instance
    have hequiv : ElementarilyEquivalent L M N := hT.models_elementarily_equivalent M N
    let : N ⊨ L[[A]].completeTheory M := (Theory.model_iff _).mpr (by
      intro σ hσ
      let τ := e.onSentence.symm σ
      have hrec : e.toLHom.onSentence τ = σ := e.onSentence.apply_symm_apply σ
      have hM : M ⊨ τ := by
        apply (e.toLHom.realize_onSentence M τ).mp
        rw [hrec]
        exact (L[[A]].mem_completeTheory).mp hσ
      have hN : N ⊨ τ := (elementarilyEquivalent_iff.mp hequiv τ).mp hM
      simpa only [hrec] using (e.toLHom.realize_onSentence N τ).mpr hN)
    refine ⟨(L[[A]].completeTheory M).typeOf a, fun φ => ?_⟩
    change Formula.equivSentence φ ∈ p ↔
      Formula.equivSentence ((L.lhomWithConstants A).onFormula φ) ∈
        (L[[A]].completeTheory M).typeOf a
    rw [← ha, Theory.CompleteType.formula_mem_typeOf,
      Theory.CompleteType.formula_mem_typeOf, LHom.realize_onFormula]
  choose f hf using lift
  refine ⟨f, fun p q hpq => ?_⟩
  apply SetLike.ext
  intro γ
  change γ ∈ p.toTheory ↔ γ ∈ q.toTheory
  let φ := Formula.equivSentence.symm γ
  have hc := (hf p φ).trans ((by rw [hpq] :
    (L.lhomWithConstants A).onFormula φ ∈ formulas (f p) ↔
      (L.lhomWithConstants A).onFormula φ ∈ formulas (f q)).trans (hf q φ).symm)
  simpa only [φ, formulas, Set.mem_preimage, Equiv.apply_symm_apply] using hc

section CountableModels
variable {L : Language.{0,0}}

/-- Smallness counts the actual shared native finite-context type spaces. -/
theorem stronglyMinimal_small (T : L.Theory) (hT : T.IsComplete)
    (hSM : StronglyMinimalSets.StronglyMinimalTheory T) [Countable L.Symbols] :
    CountableSaturatedModels.Small T := by
  intro r
  let M := hT.1.some
  obtain ⟨f, hf⟩ := native_types_empty_parameters_injection (M := M) T hT r
  have hL : L.card ≤ (ℵ₀ : Cardinal) := Cardinal.mk_le_aleph0
  have hA : #(∅ : Set M) ≤ (ℵ₀ : Cardinal) := by simp
  have hb := stronglyMinimal_finite_tuple_bound (M := M) T hT hSM
    (∅ : Set M) ℵ₀ le_rfl hL hA r
  let : Countable (TypesOver (L := L) (∅ : Set M) r) := Cardinal.mk_le_aleph0_iff.mp hb
  exact hf.countable

/-- Existence does not assert saturation of every countable model. -/
theorem stronglyMinimal_countable_saturated (T : L.Theory) (hT : T.IsComplete)
    (hSM : StronglyMinimalSets.StronglyMinimalTheory T) [Countable L.Symbols] :
    ∃ N : T.ModelType.{0,0,0}, Countable N ∧ Saturation.OmegaSaturated L N := by
  exact CountableSaturatedModels.exists_countable_saturated hT
    (stronglyMinimal_small T hT hSM)

/-- The same smallness result supplies a countable prime model. -/
theorem stronglyMinimal_countable_prime (T : L.Theory) (hT : T.IsComplete)
    (hSM : StronglyMinimalSets.StronglyMinimalTheory T) [Countable L.Symbols] :
    ∃ N : T.ModelType.{0,0,0}, Countable N ∧ AtomicAndPrimeModels.IsPrime T N := by
  exact CountableSaturatedModels.small_exists_prime hT (stronglyMinimal_small T hT hSM)

end CountableModels
end
end Lemmatheca.ModelTheory.StronglyMinimalTypes
