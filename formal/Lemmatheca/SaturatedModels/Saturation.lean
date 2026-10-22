import Lemmatheca.AtomicAndPrimeModels.PartialElementaryMaps
import Lemmatheca.TypesAndRealization.Types

/-! Finite-parameter saturation and its exact elementary-map consequences. -/

namespace Lemmatheca.ModelTheory.Saturation

open FirstOrder FirstOrder.Language
open PartialElementaryMaps

universe u v w w' z

/-- Realize actual complete one-types of each canonical finite named expansion. -/
def OmegaSaturated (L : Language.{u, v}) (M : Type w) [L.Structure M] [Nonempty M] : Prop :=
  ∀ A : Set M, A.Finite →
    ∀ q : (L[[A]].completeTheory M).CompleteType (Fin 1),
      ∃ b : Fin 1 → M, Types.Realizes (Types.formulas q) b

variable {L : Language.{u, v}} {M : Type w} {N : Type w'}
variable [L.Structure M] [L.Structure N] [Nonempty M] [Nonempty N]

theorem omega_iff_partial : OmegaSaturated L M ↔
    ∀ A : Set M, A.Finite → ∀ p : Set (L[[A]].Formula (Fin 1)),
      Types.IsPartial (L[[A]].completeTheory M) p →
        ∃ b : Fin 1 → M, Types.Realizes p b := by
  constructor
  · intro h A hA p hp
    obtain ⟨q, hpq⟩ := Types.exists_complete_extension p hp
    obtain ⟨b, hb⟩ := h A hA q
    exact ⟨b, fun φ hφ => hb φ (hpq hφ)⟩
  · intro h A hA q
    exact h A hA _ (Types.partial_formulas q)

theorem finite_omega [Finite M] : OmegaSaturated L M := by
  intro A _ q
  exact Types.finite_realization (Types.formulas q)
    ((Types.partial_iff_finitelyRealized_completeTheory _).mp (Types.partial_formulas q))

private noncomputable def namesEquiv (p : FiniteMap L M N) :
    L[[p.dom]] ≃ᴸ L[[p.range]] where
  toLHom := L.lhomWithConstantsMap p.rangeEquiv
  invLHom := L.lhomWithConstantsMap p.rangeEquiv.symm
  left_inv := by
    apply LHom.funext
    · funext n g
      cases g with
      | inl g => rfl
      | inr g =>
        cases n with
        | zero => exact congrArg Sum.inr (p.rangeEquiv.symm_apply_apply g)
        | succ n => exact g.elim
    · funext n R
      cases R with
      | inl R => rfl
      | inr R => exact R.elim
  right_inv := by
    apply LHom.funext
    · funext n g
      cases g with
      | inl g => rfl
      | inr g =>
        cases n with
        | zero => exact congrArg Sum.inr (p.rangeEquiv.apply_symm_apply g)
        | succ n => exact g.elim
    · funext n R
      cases R with
      | inl R => rfl
      | inr R => exact R.elim

omit [Nonempty M] [Nonempty N] in
private theorem named_realize (p : FiniteMap L M N) {α : Type*}
    (φ : L[[p.dom]].Formula α) (b : α → N) :
    ((namesEquiv p).onFormula φ).Realize b ↔
      Formula.Realize (BoundedFormula.constantsVarsEquiv φ) (Sum.elim p.toFun b) := by
  let : L[[p.dom]].Structure N := Diagrams.namedExpansion p.toFun
  let : (L.lhomWithConstants p.dom).IsExpansionOn N :=
    Diagrams.namedExpansion_isExpansion p.toFun
  let : (namesEquiv p).toLHom.IsExpansionOn N := by
    constructor
    · intro n g xs
      cases g with
      | inl g => rfl
      | inr g =>
        cases n with
        | zero => rfl
        | succ n => exact g.elim
    · intro n R xs
      cases R with
      | inl R => rfl
      | inr R => exact R.elim
  exact (LHom.realize_onFormula (namesEquiv p).toLHom φ).trans
    (BoundedFormula.realize_constantsVarsEquiv (φ := φ) (v := b) (xs := default)).symm

omit [Nonempty M] [Nonempty N] in
private theorem named_agreement (p : FiniteMap L M N) (σ : L[[p.dom]].Sentence) :
    M ⊨ σ ↔ N ⊨ (namesEquiv p).onSentence σ := by
  have h := p.realize_finite (BoundedFormula.constantsVarsEquiv σ)
    (Sum.elim id (Empty.elim : Empty → p.dom))
  have hm := BoundedFormula.realize_constantsVarsEquiv (M := M) (φ := σ)
    (v := (default : Empty → M)) (xs := default)
  have hn := named_realize p σ (default : Empty → N)
  have hvM : Subtype.val ∘ Sum.elim id (Empty.elim : Empty → p.dom) =
      Sum.elim (Subtype.val : p.dom → M) (default : Empty → M) := by
    funext x; cases x with
    | inl x => rfl
    | inr x => exact x.elim
  have hvN : p.toFun ∘ Sum.elim id (Empty.elim : Empty → p.dom) =
      Sum.elim p.toFun (default : Empty → N) := by
    funext x; cases x with
    | inl x => rfl
    | inr x => exact x.elim
  rw [hvM, hvN] at h
  exact hm.symm.trans (h.symm.trans hn.symm)

omit [Nonempty M] [Nonempty N] in
private theorem named_exists (p : FiniteMap L M N) {n : ℕ} {ι : Type*} [Fintype ι]
    (φ : ι → L[[p.dom]].Formula (Fin n)) :
    (∃ a : Fin n → M, ∀ i, (φ i).Realize a) ↔
      ∃ b : Fin n → N, ∀ i, ((namesEquiv p).onFormula (φ i)).Realize b := by
  let σ : L[[p.dom]].Sentence :=
    ((Formula.iInf φ).relabel (Sum.inr : Fin n → Empty ⊕ Fin n)).iExs (Fin n)
  have hm : (M ⊨ σ) ↔ ∃ a : Fin n → M, ∀ i, (φ i).Realize a := by
    simp only [σ, Sentence.Realize, Formula.realize_iExs, Formula.realize_relabel,
      Function.comp_def, Sum.elim_inr, Formula.realize_iInf]
  have hn : (N ⊨ (namesEquiv p).onSentence σ) ↔
      ∃ b : Fin n → N, ∀ i, ((namesEquiv p).onFormula (φ i)).Realize b := by
    let : L[[p.dom]].Structure N := Diagrams.namedExpansion p.toFun
    let : (namesEquiv p).toLHom.IsExpansionOn N := by
      constructor
      · intro k g xs
        cases g with
        | inl g => rfl
        | inr g =>
          cases k with
          | zero => rfl
          | succ k => exact g.elim
      · intro k R xs
        cases R with
        | inl R => rfl
        | inr R => exact R.elim
    change (N ⊨ (namesEquiv p).toLHom.onSentence σ) ↔ _
    rw [LHom.realize_onSentence]
    simp only [σ, Sentence.Realize, Formula.realize_iExs, Formula.realize_relabel,
      Function.comp_def, Sum.elim_inr, Formula.realize_iInf]
    exact exists_congr (fun b => forall_congr' (fun i =>
      (LHom.realize_onFormula (namesEquiv p).toLHom (φ i)).symm))
  exact hm.symm.trans ((named_agreement p σ).trans hn)

/-- Rename only the parameters, using the actual bijection onto the map's range. -/
noncomputable def renameFormulas (p : FiniteMap L M N) {n : ℕ} :
    L[[p.dom]].Formula (Fin n) ≃ L[[p.range]].Formula (Fin n) :=
  (namesEquiv p).onFormula

/-- Pushforward is the literal image of the original formula collection. -/
def pushFormulas (p : FiniteMap L M N) {n : ℕ}
    (q : Set (L[[p.dom]].Formula (Fin n))) : Set (L[[p.range]].Formula (Fin n)) :=
  renameFormulas p '' q

theorem pushforward_complete (p : FiniteMap L M N) {n : ℕ}
    (q : Set (L[[p.dom]].Formula (Fin n)))
    (hq : Types.IsCompletePartial (L[[p.dom]].completeTheory M) q) :
    Types.IsCompletePartial (L[[p.range]].completeTheory N) (pushFormulas p q) := by
  classical
  apply (Types.complete_iff_decides _ _).mpr
  constructor
  · apply (Types.partial_iff_finitelyRealized_completeTheory _).mpr
    intro s hs
    let t := s.image (renameFormulas p).symm
    have ht : (↑t : Set _) ⊆ q := by
      intro φ hφ
      obtain ⟨ψ, hψ, rfl⟩ := Finset.mem_image.mp hφ
      obtain ⟨θ, hθ, heq⟩ := hs hψ
      rw [← heq, Equiv.symm_apply_apply]
      exact hθ
    obtain ⟨a, ha⟩ :=
      (Types.partial_iff_finitelyRealized_completeTheory _).mp hq.1 t ht
    obtain ⟨b, hb⟩ := (named_exists p (fun ψ : s => (renameFormulas p).symm ψ)).mp
      ⟨a, fun ψ => ha _ (Finset.mem_image.mpr ⟨ψ, ψ.property, rfl⟩)⟩
    refine ⟨b, fun ψ hψ => ?_⟩
    have hh := hb ⟨ψ, hψ⟩
    change ((renameFormulas p) ((renameFormulas p).symm ψ)).Realize b at hh
    simpa only [Equiv.apply_symm_apply] using hh
  · intro φ
    rcases (Types.complete_iff_decides _ _).mp hq |>.2 ((renameFormulas p).symm φ) with h | h
    · exact Or.inl ⟨_, h, Equiv.apply_symm_apply _ _⟩
    · right
      refine ⟨_, h, ?_⟩
      change (namesEquiv p).toLHom.onBoundedFormula
        (((renameFormulas p).symm φ).not) = φ.not
      change ((renameFormulas p) ((renameFormulas p).symm φ)).not = φ.not
      rw [Equiv.apply_symm_apply]

omit [Nonempty M] [Nonempty N] in
private theorem adjoin_agreement (p : FiniteMap L M N) (a : M) (b : N)
    (h : ∀ φ : L[[p.dom]].Formula (Fin 1),
      φ.Realize (fun _ => a) ↔ (renameFormulas p φ).Realize (fun _ => b))
    {k : ℕ} (e : Fin k ≃ p.dom) (φ : L.Formula (Fin (k + 1))) :
    φ.Realize (Fin.snoc (Subtype.val ∘ e) a) ↔
      φ.Realize (Fin.snoc (p.toFun ∘ e) b) := by
  let r : Fin (k + 1) → p.dom ⊕ Fin 1 :=
    Fin.lastCases (.inr 0) (fun i => .inl (e i))
  let ψ : L[[p.dom]].Formula (Fin 1) :=
    BoundedFormula.constantsVarsEquiv.symm (φ.relabel r)
  have hrM : Sum.elim (Subtype.val : p.dom → M) (fun _ : Fin 1 => a) ∘ r =
      Fin.snoc (Subtype.val ∘ e) a := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [r]
  have hrN : Sum.elim p.toFun (fun _ : Fin 1 => b) ∘ r =
      Fin.snoc (p.toFun ∘ e) b := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [r]
  have hm := BoundedFormula.realize_constantsVarsEquiv (M := M) (φ := ψ)
    (v := fun _ => a) (xs := default)
  have hn := named_realize p ψ (fun _ => b)
  have heq : BoundedFormula.constantsVarsEquiv ψ = φ.relabel r :=
    Equiv.apply_symm_apply _ _
  rw [heq] at hm hn
  change (φ.relabel r).Realize (Sum.elim (Subtype.val : p.dom → M) (fun _ => a)) ↔
    ψ.Realize (fun _ => a) at hm
  rw [Formula.realize_relabel, hrM] at hm
  rw [Formula.realize_relabel, hrN] at hn
  exact hm.trans ((h ψ).trans hn)

omit [Nonempty M] [Nonempty N] in
private theorem adjoin_map (p : FiniteMap L M N) (a : M) (b : N)
    (h : ∀ φ : L[[p.dom]].Formula (Fin 1),
      φ.Realize (fun _ => a) ↔ (renameFormulas p φ).Realize (fun _ => b)) :
    ∃ q : FiniteMap L M N,
      q.dom = p.dom ∪ {a} ∧ q.range = p.range ∪ {b} ∧ p ≤ q ∧
        (∀ ha : a ∈ q.dom, q.toFun ⟨a, ha⟩ = b) ∧
        (a ∉ p.dom → b ∉ p.range) := by
  classical
  let := Fintype.ofFinite p.dom
  let e : Fin (Fintype.card p.dom) ≃ p.dom := (Fintype.equivFin p.dom).symm
  let c : Fin (Fintype.card p.dom + 1) → M := Fin.snoc (Subtype.val ∘ e) a
  let d : Fin (Fintype.card p.dom + 1) → N := Fin.snoc (p.toFun ∘ e) b
  let q := FiniteMap.ofTuple c d (adjoin_agreement p a b h e)
  have hdom : q.dom = p.dom ∪ {a} := by
    rw [FiniteMap.ofTuple_dom, Fin.range_snoc]
    have he : Set.range (Subtype.val ∘ e) = p.dom := by
      rw [Set.range_comp, Set.range_eq_univ.mpr e.surjective, Set.image_univ, Subtype.range_coe_subtype]
      rfl
    rw [he, Set.insert_eq, Set.union_comm]
  have hran : q.range = p.range ∪ {b} := by
    rw [FiniteMap.ofTuple_range, Fin.range_snoc]
    have he : Set.range (p.toFun ∘ e) = p.range := by
      rw [Set.range_comp, Set.range_eq_univ.mpr e.surjective, Set.image_univ]
      rfl
    rw [he, Set.insert_eq, Set.union_comm]
  have old (x : p.dom) : q.toFun ⟨x, hdom.symm ▸ Or.inl x.property⟩ = p.toFun x := by
    have hh := FiniteMap.ofTuple_apply c d (adjoin_agreement p a b h e)
      (e.symm x).castSucc
    simpa only [c, d, Fin.snoc_castSucc, Function.comp_apply, e.apply_symm_apply] using hh
  have ha : a ∈ q.dom := hdom.symm ▸ Or.inr (Set.mem_singleton a)
  have new : q.toFun ⟨a, ha⟩ = b := by
    have hh := FiniteMap.ofTuple_apply c d (adjoin_agreement p a b h e)
      (Fin.last _)
    simpa only [c, d, Fin.snoc_last] using hh
  refine ⟨q, hdom, hran, ⟨fun _ hx => hdom.symm ▸ Or.inl hx, old⟩,
    fun _ => new, ?_⟩
  intro hnot hb
  obtain ⟨x, hx⟩ := hb
  have heq := q.injective ((old x).trans (hx.trans new.symm))
  have hx : (x : M) = a := congrArg Subtype.val heq
  apply hnot
  rw [← hx]
  exact x.property

theorem one_point_extension (hN : OmegaSaturated L N) (p : FiniteMap L M N) (a : M) :
    ∃ (b : N) (q : FiniteMap L M N),
      q.dom = p.dom ∪ {a} ∧ q.range = p.range ∪ {b} ∧ p ≤ q ∧
        (∀ ha : a ∈ q.dom, q.toFun ⟨a, ha⟩ = b) ∧
        (a ∉ p.dom → b ∉ p.range) := by
  let q := Types.formulas ((L[[p.dom]].completeTheory M).typeOf (fun _ : Fin 1 => a))
  have hq : Types.IsCompletePartial (L[[p.dom]].completeTheory M) q :=
    (Types.complete_iff_mathlib _ _).mpr ⟨_, rfl, fun r hr => by
      apply SetLike.ext
      intro γ
      change γ ∈ r.toTheory ↔ γ ∈
        ((L[[p.dom]].completeTheory M).typeOf (fun _ : Fin 1 => a)).toTheory
      have hh := Set.ext_iff.mp hr (Formula.equivSentence.symm γ)
      simpa only [Types.formulas, q, Set.mem_preimage, Equiv.apply_symm_apply] using hh⟩
  obtain ⟨c, hc⟩ := (omega_iff_partial.mp hN) p.range p.finite_range
    (pushFormulas p q) (pushforward_complete p q hq).1
  let b := c 0
  have hc' : c = fun _ => b := by funext i; exact congrArg c (Subsingleton.elim _ _)
  rw [hc'] at hc
  have hh : ∀ φ : L[[p.dom]].Formula (Fin 1),
      φ.Realize (fun _ => a) ↔ (renameFormulas p φ).Realize (fun _ => b) := by
    intro φ
    constructor
    · intro ht
      exact hc _ ⟨φ, Theory.CompleteType.formula_mem_typeOf.mpr ht, rfl⟩
    · intro ht
      by_contra hn
      have hnot : φ.not ∈ q := Theory.CompleteType.formula_mem_typeOf.mpr
        (Formula.realize_not.mpr hn)
      have hn' := hc _ ⟨φ.not, hnot, rfl⟩
      exact Formula.realize_not.mp hn' ht
  obtain ⟨r, hr⟩ := adjoin_map p a b hh
  exact ⟨b, r, hr⟩

omit [Nonempty M] [Nonempty N] in
private def embeddingMap (f : M ↪ₑ[L] N) (A : Set M) (hA : A.Finite) : FiniteMap L M N where
  dom := A
  finite_dom := hA
  toFun := fun a => f a
  injective := fun _ _ h => Subtype.ext (f.injective h)
  atomic := fun φ _ a => f.map_formula φ (Subtype.val ∘ a)
  elementary := fun φ a => f.map_formula φ (Subtype.val ∘ a)

private theorem extend_finite (hN : OmegaSaturated L N) (p : FiniteMap L M N)
    (S : Set M) (hS : S.Finite) : ∃ q : FiniteMap L M N, p ≤ q ∧ S ⊆ q.dom := by
  classical
  induction S, hS using Set.Finite.induction_on with
  | empty => exact ⟨p, le_refl p, Set.empty_subset _⟩
  | @insert a S _ _ ih =>
    obtain ⟨q, hpq, hS⟩ := ih
    obtain ⟨b, r, hd, _, hqr, _⟩ := one_point_extension hN q a
    refine ⟨r, le_trans hpq hqr, ?_⟩
    intro x hx
    rcases hx with hx | hx
    · exact hd.symm ▸ Or.inr hx
    · exact FiniteMap.dom_mono hqr (hS hx)

theorem omega_iff_finite_tuples : OmegaSaturated L M ↔
    ∀ (n : ℕ) (A : Set M), A.Finite → ∀ p : Set (L[[A]].Formula (Fin n)),
      Types.IsPartial (L[[A]].completeTheory M) p →
        ∃ b : Fin n → M, Types.Realizes p b := by
  constructor
  · intro hM n A hA p hp
    have hfin := (Types.partial_iff_finitelyRealized_completeTheory _).mp hp
    obtain ⟨E, SE, hE, f, c, hc⟩ := (Types.parameter_realization A p).mp hfin
    let := SE
    let := hE
    let r := embeddingMap f A hA
    obtain ⟨q, hrq, hcq⟩ := extend_finite hM r.symm (Set.range c) (Set.finite_range c)
    let b : Fin n → M := fun i => q.toFun ⟨c i, hcq (Set.mem_range_self i)⟩
    have hAq (a : A) : f a ∈ q.dom :=
      FiniteMap.dom_mono hrq (show f a ∈ r.symm.dom from
        ⟨a, rfl⟩)
    have hfix (a : A) : q.toFun ⟨f a, hAq a⟩ = a := by
      have h₁ := FiniteMap.map_mono hrq (r.rangeEquiv a)
      have h₂ := r.symm_apply a
      exact h₁.trans h₂
    refine ⟨b, fun φ hφ => ?_⟩
    let t : A ⊕ Fin n → q.dom := Sum.elim
      (fun a => ⟨f a, hAq a⟩) (fun i => ⟨c i, hcq (Set.mem_range_self i)⟩)
    let : Finite A := hA.to_subtype
    have h := q.realize_finite (BoundedFormula.constantsVarsEquiv φ) t
    have hsrc : Subtype.val ∘ t = Sum.elim (fun a : A => f a) c := by
      funext x; cases x <;> rfl
    have htgt : q.toFun ∘ t = Sum.elim (Subtype.val : A → M) b := by
      funext x
      cases x with
      | inl a => exact hfix a
      | inr i => rfl
    rw [hsrc, htgt] at h
    have he := Types.parameterFormula_realize f A φ c
    rw [Types.parameterFormula, Formula.realize_relabel] at he
    have hctx : Sum.elim f c ∘ Sum.map (Subtype.val : A → M) id =
        Sum.elim (fun a : A => f a) c := by funext x; cases x <;> rfl
    rw [hctx] at he
    have hm := BoundedFormula.realize_constantsVarsEquiv (M := M) (φ := φ)
      (v := b) (xs := default)
    exact hm.mp (h.mpr (he.mpr (hc φ hφ)))
  · intro h
    apply omega_iff_partial.mpr
    exact h 1

theorem finite_constant_expansion (hM : OmegaSaturated L M) (ι : Type z) [Finite ι]
    [L[[ι]].Structure M] [(L.lhomWithConstants ι).IsExpansionOn M] :
    OmegaSaturated L[[ι]] M := by
  classical
  apply omega_iff_partial.mpr
  intro A hA p hp
  let D : Set M := A ∪ Set.range (fun i : ι => (L.con i : M))
  have hD : D.Finite := hA.union (Set.finite_range _)
  let c : ι → D := fun i => ⟨L.con i, Or.inr (Set.mem_range_self i)⟩
  let a : A → D := fun x => ⟨x, Or.inl x.property⟩
  let k : (L[[ι]])[[A]] →ᴸ L[[D]] :=
    LHom.sumElim (L.lhomWithConstantsMap c)
      ((LHom.sumInr : constantsOn D →ᴸ L[[D]]).comp (LHom.constantsOnMap a))
  let : k.IsExpansionOn M := by
    constructor
    · intro n g xs
      cases g with
      | inl g =>
        cases g with
        | inl g =>
          exact ((L.lhomWithConstants ι).map_onFunction g xs).symm
        | inr i =>
          cases n with
          | zero =>
            change (↑(L.con (show ι from i)) : M) =
              @Structure.funMap L[[ι]] M _ 0 (Sum.inr i) xs
            rw [Unique.eq_default xs]
            rfl
          | succ n => exact i.elim
      | inr x =>
        cases n with
        | zero => rfl
        | succ n => exact x.elim
    · intro n R xs
      cases R with
      | inl R =>
        cases R with
        | inl R => exact ((L.lhomWithConstants ι).map_onRelation R xs).symm
        | inr R => exact R.elim
      | inr R => exact R.elim
  let p' : Set (L[[D]].Formula (Fin 1)) := k.onFormula '' p
  have hp' : Types.IsPartial (L[[D]].completeTheory M) p' := by
    apply (Types.partial_iff_finitelyRealized_completeTheory _).mpr
    intro s hs
    let pick (ψ : s) := Classical.choose (hs ψ.property)
    have hpick (ψ : s) : pick ψ ∈ p ∧ k.onFormula (pick ψ) = ψ :=
      Classical.choose_spec (hs ψ.property)
    let t := s.attach.image pick
    obtain ⟨b, hb⟩ := (Types.partial_iff_finitelyRealized_completeTheory _).mp hp t (by
      rintro φ hφ
      obtain ⟨ψ, _, rfl⟩ := Finset.mem_image.mp hφ
      exact (hpick ψ).1)
    refine ⟨b, fun ψ hψ => ?_⟩
    have hh := (LHom.realize_onFormula k (pick ⟨ψ, hψ⟩)).mpr
      (hb _ (Finset.mem_image.mpr ⟨⟨ψ, hψ⟩, Finset.mem_attach _ _, rfl⟩))
    rwa [(hpick ⟨ψ, hψ⟩).2] at hh
  obtain ⟨b, hb⟩ := (omega_iff_partial.mp hM) D hD p' hp'
  exact ⟨b, fun φ hφ => (LHom.realize_onFormula k φ).mp (hb _ ⟨φ, hφ, rfl⟩)⟩

theorem finite_names (hM : OmegaSaturated L M) (C : Set M) (hC : C.Finite) :
    OmegaSaturated L[[C]] M := by
  let : Finite C := hC.to_subtype
  exact finite_constant_expansion hM C

private theorem complete_formulas {K : Language} {T : K.Theory} {α : Type*}
    (q : T.CompleteType α) : Types.IsCompletePartial T (Types.formulas q) := by
  apply (Types.complete_iff_decides _ _).mpr
  refine ⟨Types.partial_formulas q, fun φ => ?_⟩
  rcases q.mem_or_not_mem (Formula.equivSentence φ) with h | h
  · exact Or.inl h
  · exact Or.inr h

private theorem iso_forward (h : M ≃[L] N) (hM : OmegaSaturated L M) :
    OmegaSaturated L N := by
  apply omega_iff_partial.mpr
  intro A hA t ht
  obtain ⟨q, htq⟩ := Types.exists_complete_extension t ht
  let p := embeddingMap h.symm.toElementaryEmbedding A hA
  obtain ⟨b, hb⟩ := (omega_iff_partial.mp hM) p.range p.finite_range
    (pushFormulas p (Types.formulas q))
    (pushforward_complete p _ (complete_formulas q)).1
  refine ⟨h ∘ b, fun φ hφ => ?_⟩
  have hr := (named_realize p φ b).mp (hb _ ⟨φ, htq hφ, rfl⟩)
  change Formula.Realize (BoundedFormula.constantsVarsEquiv φ)
    (Sum.elim (fun x : A => h.symm x) b) at hr
  have hh := h.toElementaryEmbedding.map_formula (BoundedFormula.constantsVarsEquiv φ)
    (Sum.elim (fun x : A => h.symm x) b)
  have hctx : h ∘ Sum.elim (fun x : A => h.symm x) b =
      Sum.elim (Subtype.val : A → N) (h ∘ b) := by
    funext x
    cases x with
    | inl x => exact h.apply_symm_apply x
    | inr i => rfl
  change Formula.Realize (BoundedFormula.constantsVarsEquiv φ)
    (h ∘ Sum.elim (fun x : A => h.symm x) b) ↔ _ at hh
  rw [hctx] at hh
  exact (BoundedFormula.realize_constantsVarsEquiv (M := N) (φ := φ)
    (v := h ∘ b) (xs := default)).mp (hh.mpr hr)

theorem isomorphism_invariant (h : M ≃[L] N) :
    OmegaSaturated L M ↔ OmegaSaturated L N := by
  exact ⟨iso_forward h, iso_forward h.symm⟩

theorem countable_embedding [Countable M] (hN : OmegaSaturated L N)
    (p : FiniteMap L M N) :
    ∃ e : M ↪ₑ[L] N, ∀ a : p.dom, e a = p.toFun a := by
  apply FiniteMap.countable_embedding _ p
  intro q a
  obtain ⟨b, r, hd, _, hqr, _⟩ := one_point_extension hN q a
  exact ⟨r, hqr, hd.symm ▸ Or.inr (Set.mem_singleton a)⟩

theorem countable_isomorphism [Countable M] [Countable N]
    (hM : OmegaSaturated L M) (hN : OmegaSaturated L N) (p : FiniteMap L M N) :
    ∃ e : M ≃[L] N, ∀ a : p.dom, e a = p.toFun a := by
  let S : BackAndForth.BackForthSystem L M N := {
    maps := Set.range (fun q : FiniteMap L M N => q.toFinitePartialIso)
    nonempty := ⟨p.toFinitePartialIso, p, rfl⟩
    forth := by
      rintro _ ⟨q, rfl⟩ a
      obtain ⟨b, r, hd, _, hqr, _⟩ := one_point_extension hN q a
      exact ⟨r.toFinitePartialIso, ⟨r, rfl⟩, hqr,
        hd.symm ▸ Or.inr (Set.mem_singleton a)⟩
    back := by
      rintro _ ⟨q, rfl⟩ b
      obtain ⟨a, r, hd, _, hqr, hrb, _⟩ := one_point_extension hM q.symm b
      have hq : q ≤ r.symm := by
        have h' := FiniteMap.symm_le_symm hqr
        rwa [FiniteMap.symm_symm] at h'
      have hb : b ∈ r.dom := hd.symm ▸ Or.inr (Set.mem_singleton b)
      exact ⟨r.symm.toFinitePartialIso, ⟨r.symm, rfl⟩, hq,
        r.rangeEquiv ⟨b, hb⟩, r.symm_apply ⟨b, hb⟩⟩ }
  exact BackAndForth.countable_isomorphism S p.toFinitePartialIso ⟨p, rfl⟩

theorem homogeneity [Countable M] (hM : OmegaSaturated L M)
    (A : Set M) (hA : A.Finite) {n : ℕ} (a b : Fin n → M)
    (htype : (L[[A]].completeTheory M).typeOf a = (L[[A]].completeTheory M).typeOf b) :
    ∃ g : M ≃[L] M, (∀ c ∈ A, g c = c) ∧ ∀ i, g (a i) = b i := by
  have hab : ∀ φ : L[[A]].Formula (Fin n), φ.Realize a ↔ φ.Realize b := by
    intro φ
    have ha : Formula.equivSentence φ ∈ ((L[[A]].completeTheory M).typeOf a) ↔
        φ.Realize a := Theory.CompleteType.formula_mem_typeOf
    have hb : Formula.equivSentence φ ∈ ((L[[A]].completeTheory M).typeOf b) ↔
        φ.Realize b := Theory.CompleteType.formula_mem_typeOf
    rw [htype] at ha
    exact ha.symm.trans hb
  let p := FiniteMap.ofTuple a b hab
  have hMA := finite_names hM A hA
  obtain ⟨e, he⟩ := countable_isomorphism hMA hMA p
  let g : M ≃[L] M := { e.toEquiv with
    map_fun' := by
      intro n f x
      exact e.map_fun (Sum.inl f : L[[A]].Functions n) x
    map_rel' := by
      intro n R x
      exact e.map_rel (Sum.inl R : L[[A]].Relations n) x }
  refine ⟨g, ?_, fun i => ?_⟩
  · intro c hc
    change e c = c
    exact e.map_constants (L.con (⟨c, hc⟩ : A))
  · change e (a i) = b i
    exact (he ⟨a i, Set.mem_range_self i⟩).trans (FiniteMap.ofTuple_apply a b hab i)

end Lemmatheca.ModelTheory.Saturation
