import Lemmatheca.CardinalSaturationAndHomogeneity.Adjoin
import Lemmatheca.SaturatedModels.Saturation
import Mathlib.SetTheory.Cardinal.Aleph
import Mathlib.SetTheory.Cardinal.Arithmetic

/-! Native named types over parameter sets bounded by an arbitrary infinite cardinal. -/

namespace Lemmatheca.ModelTheory.CardinalSaturation

open FirstOrder FirstOrder.Language
open PartialElementaryMaps
open Cardinal

universe u v w w' z z'

noncomputable section

/-- Universe-independent strict comparison of a carrier with a cardinal. -/
def Below (κ : Cardinal.{z}) (X : Type w) : Prop :=
  Cardinal.lift.{z} (#X) < Cardinal.lift.{w} κ

/-- Universe-independent weak comparison of a carrier with a cardinal. -/
def AtMost (κ : Cardinal.{z}) (X : Type w) : Prop :=
  Cardinal.lift.{z} (#X) ≤ Cardinal.lift.{w} κ

/-- Realize actual complete one-types in each canonical named expansion. -/
def IsSaturated (κ : Cardinal.{z}) (L : Language.{u, v}) (M : Type w)
    [L.Structure M] [Nonempty M] : Prop :=
  ∀ A : Set M, Below κ A →
    ∀ q : (L[[A]].completeTheory M).CompleteType (Fin 1),
      ∃ b : Fin 1 → M, Types.Realizes (Types.formulas q) b

/-- The saturated-model convention for an infinite carrier. -/
def SaturatedModel (L : Language.{u, v}) (M : Type w)
    [L.Structure M] [Nonempty M] [Infinite M] : Prop :=
  IsSaturated (#M) L M

variable {L : Language.{u, v}} {M : Type w} {N : Type w'}
variable [L.Structure M] [L.Structure N] [Nonempty M] [Nonempty N]
variable {κ μ : Cardinal.{z}}

theorem below_equiv {X : Type w} {Y : Type w'} (e : X ≃ Y) :
    Below κ X ↔ Below κ Y := by
  unfold Below
  have he := Cardinal.lift_mk_eq.{w, w', z}.mpr ⟨e⟩
  constructor
  · intro h
    have h' : Cardinal.lift.{w'} (Cardinal.lift.{z} (#X)) <
        Cardinal.lift.{w'} (Cardinal.lift.{w} κ) := Cardinal.lift_lt.mpr h
    simp only [Cardinal.lift_lift] at h'
    rw [he] at h'
    apply Cardinal.lift_lt.{max w' z, w}.mp
    simpa only [Cardinal.lift_lift] using h'
  · intro h
    have h' : Cardinal.lift.{w} (Cardinal.lift.{z} (#Y)) <
        Cardinal.lift.{w} (Cardinal.lift.{w'} κ) := Cardinal.lift_lt.mpr h
    simp only [Cardinal.lift_lift] at h'
    rw [← he] at h'
    apply Cardinal.lift_lt.{max w z, w'}.mp
    simpa only [Cardinal.lift_lift] using h'

omit [Nonempty M] in
theorem below_insert (hκ : ℵ₀ ≤ κ) (A : Set M) (hA : Below κ A) (a : M) :
    Below κ (insert a A : Set M) := by
  unfold Below at *
  have hinf : ℵ₀ ≤ Cardinal.lift.{w} κ := by simpa using Cardinal.lift_le.{w}.mpr hκ
  have hsize := Cardinal.lift_le.{z}.mpr (Cardinal.mk_insert_le (s := A) (a := a))
  rw [Cardinal.lift_add, Cardinal.lift_one] at hsize
  exact hsize.trans_lt (Cardinal.add_one_lt_of_lt hinf hA)

omit [Nonempty M] in
theorem below_union_finite (hκ : ℵ₀ ≤ κ) (A C : Set M)
    (hA : Below κ A) (hC : C.Finite) : Below κ (A ∪ C : Set M) := by
  unfold Below at *
  have hinf : ℵ₀ ≤ Cardinal.lift.{w} κ := by simpa using Cardinal.lift_le.{w}.mpr hκ
  have hc : Cardinal.lift.{z} (#C) < ℵ₀ := by
    simpa only [Cardinal.lift_lt_aleph0, Cardinal.lt_aleph0_iff_set_finite] using hC
  have hsize := Cardinal.lift_le.{z}.mpr (Cardinal.mk_union_le A C)
  rw [Cardinal.lift_add] at hsize
  exact hsize.trans_lt (Cardinal.add_lt_of_lt hinf hA (hc.trans_le hinf))

theorem monotone (hμκ : μ ≤ κ) (hM : IsSaturated κ L M) :
    IsSaturated μ L M := by
  intro A hA q
  apply hM A _ q
  exact hA.trans_le (Cardinal.lift_le.mpr hμκ)

theorem aleph_zero_iff : IsSaturated (ℵ₀ : Cardinal.{z}) L M ↔
    Saturation.OmegaSaturated L M := by
  unfold IsSaturated Saturation.OmegaSaturated
  have hsmall (A : Set M) : Below (ℵ₀ : Cardinal.{z}) A ↔ A.Finite := by
    simp only [Below, Cardinal.lift_aleph0, Cardinal.lift_lt_aleph0,
      Cardinal.lt_aleph0_iff_set_finite]
  simp_rw [hsmall]

theorem aleph_one_iff : IsSaturated (ℵ_ 1 : Cardinal.{z}) L M ↔
    ∀ A : Set M, A.Countable →
      ∀ q : (L[[A]].completeTheory M).CompleteType (Fin 1),
        ∃ b : Fin 1 → M, Types.Realizes (Types.formulas q) b := by
  unfold IsSaturated
  have hsmall (A : Set M) : Below (ℵ_ 1 : Cardinal.{z}) A ↔ A.Countable := by
    simp only [Below, Cardinal.lift_aleph, Ordinal.lift_one,
      Cardinal.lt_aleph_one_iff, Cardinal.lift_le_aleph0,
      Cardinal.le_aleph0_iff_set_countable]
  simp_rw [hsmall]

theorem finite_saturated [Finite M] (κ : Cardinal.{z}) : IsSaturated κ L M := by
  intro A _ q
  exact Types.finite_realization (Types.formulas q)
    ((Types.partial_iff_finitelyRealized_completeTheory _).mp (Types.partial_formulas q))

/-- Restrict a given elementary embedding to an arbitrary actual parameter set. -/
def embeddingMap (f : M ↪ₑ[L] N) (A : Set M) : Map L M N where
  dom := A
  toFun := fun a => f a.val
  injective := fun _ _ h => Subtype.ext (f.injective h)
  elementary := fun φ a => f.map_formula φ (Subtype.val ∘ a)

/-- Replace exactly the old parameter names, leaving free variables fixed. -/
def renameFormulas (p : Map L M N) {α : Type z'} :
    L[[p.dom]].Formula α ≃ L[[p.range]].Formula α :=
  BoundedFormula.constantsVarsEquiv.trans
    ((BoundedFormula.relabelEquiv
      (Equiv.sumCongr p.rangeEquiv (Equiv.refl α))).trans
      BoundedFormula.constantsVarsEquiv.symm)

/-- The pushforward is the literal image under the specified map's renaming. -/
def pushFormulas (p : Map L M N) {α : Type z'}
    (q : Set (L[[p.dom]].Formula α)) : Set (L[[p.range]].Formula α) :=
  renameFormulas p '' q

omit [Nonempty M] [Nonempty N] in
theorem named_realize (p : Map L M N) {α : Type z'}
    (φ : L[[p.dom]].Formula α) (b : α → N) :
    (renameFormulas p φ).Realize b ↔
      Formula.Realize (BoundedFormula.constantsVarsEquiv φ) (Sum.elim p.toFun b) := by
  have h := BoundedFormula.realize_constantsVarsEquiv (M := N)
    (φ := renameFormulas p φ) (v := b) (xs := default)
  have hc : BoundedFormula.constantsVarsEquiv (renameFormulas p φ) =
      BoundedFormula.relabelEquiv (Equiv.sumCongr p.rangeEquiv (Equiv.refl α))
        (BoundedFormula.constantsVarsEquiv φ) := by
    simp only [renameFormulas, Equiv.trans_apply, Equiv.apply_symm_apply]
  rw [hc, BoundedFormula.realize_relabelEquiv] at h
  have heq : Sum.elim (fun a : p.range => (L.con a : N)) b ∘
      Equiv.sumCongr p.rangeEquiv (Equiv.refl α) = Sum.elim p.toFun b := by
    funext x
    cases x <;> rfl
  rw [heq] at h
  exact h.symm

omit [Nonempty M] [Nonempty N] in
theorem named_agreement (p : Map L M N) (σ : L[[p.dom]].Sentence) :
    M ⊨ σ ↔ N ⊨ renameFormulas p σ := by
  have h := p.realize_formula (BoundedFormula.constantsVarsEquiv σ)
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
theorem named_exists (p : Map L M N) {n : ℕ} {ι : Type z'} [Fintype ι]
    (φ : ι → L[[p.dom]].Formula (Fin n)) :
    (∃ a : Fin n → M, ∀ i, (φ i).Realize a) ↔
      ∃ b : Fin n → N, ∀ i, (renameFormulas p (φ i)).Realize b := by
  let ψ : L.Formula p.dom :=
    (Formula.iInf (fun i => BoundedFormula.constantsVarsEquiv (φ i))).iExs (Fin n)
  have h := p.realize_formula ψ id
  simp only [ψ, Function.comp_id, Formula.realize_iExs, Formula.realize_iInf] at h
  constructor
  · rintro ⟨a, ha⟩
    have ha' : ∀ i, Formula.Realize (BoundedFormula.constantsVarsEquiv (φ i))
        (Sum.elim (Subtype.val : p.dom → M) a) := by
      intro i
      exact (BoundedFormula.realize_constantsVarsEquiv (M := M) (φ := φ i)
        (v := a) (xs := default)).mpr (ha i)
    obtain ⟨b, hb⟩ := h.mpr ⟨a, ha'⟩
    exact ⟨b, fun i => (named_realize p (φ i) b).mpr (hb i)⟩
  · rintro ⟨b, hb⟩
    obtain ⟨a, ha⟩ := h.mp ⟨b, fun i => (named_realize p (φ i) b).mp (hb i)⟩
    exact ⟨a, fun i => (BoundedFormula.realize_constantsVarsEquiv (M := M)
      (φ := φ i) (v := a) (xs := default)).mp (ha i)⟩

omit [Nonempty M] [Nonempty N] in
theorem rename_not (p : Map L M N) {α : Type z'} (φ : L[[p.dom]].Formula α) :
    renameFormulas p φ.not = (renameFormulas p φ).not := by
  rfl

theorem pushforward_complete (p : Map L M N) {n : ℕ}
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
      rw [rename_not, Equiv.apply_symm_apply]

theorem pushforward_type (p : Map L M N) {n : ℕ}
    (q : (L[[p.dom]].completeTheory M).CompleteType (Fin n)) :
    ∃ q' : (L[[p.range]].completeTheory N).CompleteType (Fin n),
      Types.formulas q' = pushFormulas p (Types.formulas q) := by
  have hq : Types.IsCompletePartial (L[[p.dom]].completeTheory M) (Types.formulas q) :=
    (Types.complete_iff_decides _ _).mpr ⟨Types.partial_formulas q, fun φ => by
      rcases q.mem_or_not_mem (Formula.equivSentence φ) with h | h
      · exact Or.inl h
      · exact Or.inr h⟩
  obtain ⟨q', hq', _⟩ := (Types.complete_iff_mathlib _ _).mp
    (pushforward_complete p _ hq)
  exact ⟨q', hq'⟩

omit [Nonempty N] in
theorem realized_type_match (p : Map L M N) (a : M) (b : N)
    (hb : Types.Realizes
      (pushFormulas p (Types.formulas ((L[[p.dom]].completeTheory M).typeOf
        (fun _ : Fin 1 => a)))) (fun _ : Fin 1 => b)) :
    PointMatch p a b := by
  have hh (ψ : L[[p.dom]].Formula (Fin 1)) :
      ψ.Realize (fun _ => a) ↔ (renameFormulas p ψ).Realize (fun _ => b) := by
    constructor
    · intro ht
      exact hb _ ⟨ψ, Theory.CompleteType.formula_mem_typeOf.mpr ht, rfl⟩
    · intro ht
      by_contra hn
      have hnot : ψ.not ∈ Types.formulas
          ((L[[p.dom]].completeTheory M).typeOf (fun _ : Fin 1 => a)) :=
        Theory.CompleteType.formula_mem_typeOf.mpr (Formula.realize_not.mpr hn)
      have hn' := hb _ ⟨ψ.not, hnot, rfl⟩
      rw [rename_not] at hn'
      exact Formula.realize_not.mp hn' ht
  intro φ
  let ψ : L[[p.dom]].Formula (Fin 1) := BoundedFormula.constantsVarsEquiv.symm φ
  have hm := BoundedFormula.realize_constantsVarsEquiv (M := M) (φ := ψ)
    (v := fun _ : Fin 1 => a) (xs := default)
  have hn := named_realize p ψ (fun _ : Fin 1 => b)
  have heq : BoundedFormula.constantsVarsEquiv ψ = φ := Equiv.apply_symm_apply _ _
  rw [heq] at hm hn
  exact hm.trans ((hh ψ).trans hn)

omit [Nonempty N] in
theorem realized_type_fresh (p : Map L M N) (a : M) (ha : a ∉ p.dom) (b : N)
    (hb : Types.Realizes
      (pushFormulas p (Types.formulas ((L[[p.dom]].completeTheory M).typeOf
        (fun _ : Fin 1 => a)))) (fun _ : Fin 1 => b)) :
    b ∉ p.range := by
  rintro ⟨d, hd⟩
  let φ : L.Formula (p.dom ⊕ Fin 1) :=
    (Term.var (Sum.inr 0)).equal (Term.var (Sum.inl d))
  have h := (realized_type_match p a b hb φ).mpr
    (show φ.Realize (Sum.elim p.toFun (fun _ : Fin 1 => b)) from by
      simpa only [φ, Formula.realize_equal, Term.realize_var, Sum.elim_inr,
        Sum.elim_inl] using hd.symm)
  have had : a = d.val := by
    simpa only [φ, Formula.realize_equal, Term.realize_var, Sum.elim_inr,
      Sum.elim_inl] using h
  exact ha (had.symm ▸ d.property)

theorem one_point_extension (hκ : ℵ₀ ≤ κ) (hN : IsSaturated κ L N)
    (p : Map L M N) (hp : Below κ p.dom) (a : M) :
    ∃ (b : N) (q : Map L M N),
      q.dom = insert a p.dom ∧ q.range = insert b p.range ∧ p ≤ q ∧
      (∀ ha : a ∈ q.dom, q.toFun ⟨a, ha⟩ = b) ∧
      (a ∉ p.dom → b ∉ p.range) ∧ Below κ q.dom ∧ Below κ q.range := by
  classical
  have hprange : Below κ p.range := (below_equiv p.rangeEquiv).mp hp
  by_cases ha : a ∈ p.dom
  · let b := p.toFun ⟨a, ha⟩
    have hb : b ∈ p.range := ⟨⟨a, ha⟩, rfl⟩
    refine ⟨b, p, (Set.insert_eq_of_mem ha).symm, (Set.insert_eq_of_mem hb).symm,
      le_refl p, ?_, ?_, hp, hprange⟩
    · intro _
      rfl
    · exact fun h => False.elim (h ha)
  · let q := (L[[p.dom]].completeTheory M).typeOf (fun _ : Fin 1 => a)
    obtain ⟨q', hq'⟩ := pushforward_type p q
    obtain ⟨c, hc⟩ := hN p.range hprange q'
    rw [hq'] at hc
    let b := c 0
    have hcb : c = fun _ => b := by
      funext i
      exact congrArg c (Subsingleton.elim _ _)
    rw [hcb] at hc
    have hmatch := realized_type_match p a b hc
    have hfresh := realized_type_fresh p a ha b hc
    let r := adjoinMap p a b ha hfresh hmatch
    obtain ⟨hpr, hd, hr, hv⟩ := adjoin_map_spec p a b ha hfresh hmatch
    refine ⟨b, r, hd, hr, hpr, ?_, fun _ => hfresh, ?_, ?_⟩
    · intro _
      exact hv
    · rw [hd]
      exact below_insert hκ p.dom hp a
    · rw [hr]
      exact below_insert hκ p.range hprange b

theorem finite_set_extension (hκ : ℵ₀ ≤ κ) (hN : IsSaturated κ L N)
    (p : Map L M N) (hp : Below κ p.dom) (C : Set M) (hC : C.Finite) :
    ∃ q : Map L M N, p ≤ q ∧ C ⊆ q.dom ∧ Below κ q.dom := by
  classical
  induction C, hC using Set.Finite.induction_on with
  | empty => exact ⟨p, le_refl p, Set.empty_subset _, hp⟩
  | @insert a C _ _ ih =>
    obtain ⟨q, hpq, hCq, hq⟩ := ih
    obtain ⟨b, r, hd, _, hqr, _, _, hr, _⟩ := one_point_extension hκ hN q hq a
    refine ⟨r, le_trans hpq hqr, ?_, hr⟩
    intro x hx
    rcases hx with hx | hx
    · exact hd.symm ▸ Or.inl hx
    · exact Map.dom_mono hqr (hCq hx)

theorem finite_tuple_test (hκ : ℵ₀ ≤ κ) : IsSaturated κ L M ↔
    ∀ (n : ℕ) (A : Set M), Below κ A →
      ∀ p : Set (L[[A]].Formula (Fin n)),
        Types.IsPartial (L[[A]].completeTheory M) p →
          ∃ b : Fin n → M, Types.Realizes p b := by
  constructor
  · intro hM n A hA p hp
    have hfin := (Types.partial_iff_finitelyRealized_completeTheory _).mp hp
    obtain ⟨E, SE, hE, f, c, hc⟩ := (Types.parameter_realization A p).mp hfin
    let := SE
    let := hE
    let r := embeddingMap f A
    have hrs : Below κ r.symm.dom := (below_equiv r.rangeEquiv).mp hA
    obtain ⟨q, hrq, hcq, _⟩ :=
      finite_set_extension hκ hM r.symm hrs (Set.range c) (Set.finite_range c)
    let b : Fin n → M := fun i => q.toFun ⟨c i, hcq (Set.mem_range_self i)⟩
    have hAq (a : A) : f a ∈ q.dom :=
      Map.dom_mono hrq (show f a ∈ r.symm.dom from ⟨a, rfl⟩)
    have hfix (a : A) : q.toFun ⟨f a, hAq a⟩ = a := by
      have h₁ := Map.apply_mono hrq (r.rangeEquiv a)
      have h₂ := r.symm_apply a
      exact h₁.trans h₂
    refine ⟨b, fun φ hφ => ?_⟩
    let t : A ⊕ Fin n → q.dom := Sum.elim
      (fun a => ⟨f a, hAq a⟩) (fun i => ⟨c i, hcq (Set.mem_range_self i)⟩)
    have h := q.realize_formula (BoundedFormula.constantsVarsEquiv φ) t
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
  · intro h A hA q
    exact h 1 A hA (Types.formulas q) (Types.partial_formulas q)

end
end Lemmatheca.ModelTheory.CardinalSaturation
