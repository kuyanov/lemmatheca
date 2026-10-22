import Lemmatheca.IsolatedTypes.IsolatedTypes
import Lemmatheca.OmittingTypes.OmittingTypes

/-! Atomic types and their finite-parameter descriptions, in the existing first-order syntax. -/

namespace Lemmatheca.ModelTheory.AtomicAndPrimeModels

open FirstOrder FirstOrder.Language
open Lemmatheca.ModelTheory.Types Lemmatheca.ModelTheory.IsolatedTypes
open scoped FirstOrder

variable {L : Language.{0, 0}} {T : L.Theory}

/-- Every complete type of a realized finite tuple has an isolating formula. -/
def IsAtomic (T : L.Theory) (M : Type) [L.Structure M] [Nonempty M] [M ⊨ T] : Prop :=
  ∀ (n : ℕ) (a : Fin n → M), Isolated T (T.typeOf a)

/-- A prime structure admits an elementary embedding into every nonempty model of the theory. -/
def IsPrime (T : L.Theory) (M : Type) [L.Structure M] : Prop :=
  ∀ N : Theory.ModelType.{0, 0, 0} T, Nonempty (M ↪ₑ[L] N)

/-- Naming exactly the indicated old elements keeps their intended interpretations. -/
abbrev NamedModel (L : Language.{0, 0}) (M : Type) [L.Structure M] (A : Set M) :=
  (Embedding.refl L M).withConstants A

instance {M : Type} [L.Structure M] [Nonempty M] (A : Set M) :
    Nonempty (NamedModel L M A) := inferInstanceAs (Nonempty M)

/-- Isolation over a finite or infinite set is isolation in the complete theory of its named model. -/
def IsolatedOver {M : Type} [L.Structure M] [Nonempty M]
    (A : Set M) {n : ℕ} (b : Fin n → M) : Prop :=
  Isolated (L[[A]].completeTheory (NamedModel L M A))
    ((L[[A]].completeTheory (NamedModel L M A)).typeOf (M := NamedModel L M A) (fun i => b i))

private def IsolatesAt {α : Type} {M : Type} [L.Structure M]
    (T : L.Theory) (a : α → M) (θ : L.Formula α) : Prop :=
  θ.Realize a ∧ ∀ φ, φ.Realize a → T ⊨ᵇ θ.imp φ

private theorem isolatesAt_iff {M : Type} [L.Structure M] [Nonempty M] [M ⊨ T]
    {n : ℕ} (a : Fin n → M) (θ : L.Formula (Fin n)) :
    Isolates T (T.typeOf a) θ ↔ IsolatesAt T a θ := by
  constructor
  · rintro ⟨hθ, h⟩
    exact ⟨Theory.CompleteType.formula_mem_typeOf.mp hθ,
      fun φ hφ => h φ (Theory.CompleteType.formula_mem_typeOf.mpr hφ)⟩
  · rintro ⟨hθ, h⟩
    exact ⟨Theory.CompleteType.formula_mem_typeOf.mpr hθ,
      fun φ hφ => h φ (Theory.CompleteType.formula_mem_typeOf.mp hφ)⟩

private theorem complete_models_formula {M : Type} [L.Structure M] [Nonempty M]
    {α : Type} [Finite α] (φ : L.Formula α) :
    L.completeTheory M ⊨ᵇ φ ↔ ∀ a : α → M, φ.Realize a := by
  constructor
  · intro h a
    exact h.realize_formula M
  · intro h
    let σ : L.Sentence := (φ.relabel Sum.inr).iAlls α
    have hσ : M ⊨ σ := by
      simpa only [σ, Sentence.Realize, Formula.realize_iAlls, Formula.realize_relabel,
        Function.comp_def, Sum.elim_inr] using h
    have hmod : L.completeTheory M ⊨ᵇ σ := Theory.models_sentence_of_mem hσ
    apply Theory.models_formula_iff.mpr
    intro N a
    have hn := hmod.realize_sentence N
    have hall : ∀ b : α → N, φ.Realize b := by
      simpa only [σ, Sentence.Realize, Formula.realize_iAlls, Formula.realize_relabel,
        Function.comp_def, Sum.elim_inr] using hn
    exact hall a

private theorem reindex_isolatesAt {M : Type} [L.Structure M] {α β : Type}
    (e : α ≃ β) (a : α → M) (θ : L.Formula α) (h : IsolatesAt T a θ) :
    IsolatesAt T (a ∘ e.symm) (θ.relabel e) := by
  constructor
  · simpa only [Formula.realize_relabel, Function.comp_assoc, e.symm_comp_self,
      Function.comp_id] using h.1
  · intro φ hφ
    have hφa : (φ.relabel e.symm).Realize a := by
      simpa only [Formula.realize_relabel] using hφ
    apply Theory.models_formula_iff.mpr
    intro N b
    change (θ.relabel e).Realize b → φ.Realize b
    intro hθb
    have hθN : θ.Realize (b ∘ e) := by
      simpa only [Formula.realize_relabel] using hθb
    have hφb : (φ.relabel e.symm).Realize (b ∘ e) :=
      (h.2 _ hφa).realize_formula N hθN
    simpa only [Formula.realize_relabel, Function.comp_assoc, e.self_comp_symm,
      Function.comp_id] using hφb

private theorem sum_assignment {X : Type} {m n : ℕ} (a : Fin m → X) (b : Fin n → X) :
    Fin.append a b ∘ finSumFinEquiv = Sum.elim a b := by
  funext x
  cases x <;> simp

private noncomputable def nameTuple {M : Type} {m n : ℕ} (a : Fin m → M)
    (θ : L.Formula (Fin m ⊕ Fin n)) : L[[Set.range a]].Formula (Fin n) :=
  BoundedFormula.constantsVarsEquiv.symm
    (θ.relabel (Sum.map (fun i => (⟨a i, ⟨i, rfl⟩⟩ : Set.range a)) id))

private theorem nameTuple_realize {M : Type} [L.Structure M] {m n : ℕ}
    (a : Fin m → M) (θ : L.Formula (Fin m ⊕ Fin n)) (b : Fin n → M) :
    @Formula.Realize _ (NamedModel L M (Set.range a)) _ _ (nameTuple a θ) b ↔
      θ.Realize (Sum.elim a b) := by
  have h := parameterFormula_realize (ElementaryEmbedding.refl L M)
    (Set.range a) (nameTuple a θ) b
  rw [parameterFormula, nameTuple, Equiv.apply_symm_apply,
    Formula.realize_relabel, Formula.realize_relabel] at h
  have he : ((Sum.elim (id : M → M) b) ∘ Sum.map (Subtype.val : Set.range a → M) id) ∘
      Sum.map (fun i => (⟨a i, ⟨i, rfl⟩⟩ : Set.range a)) id = Sum.elim a b := by
    funext x
    cases x <;> rfl
  change θ.Realize (((Sum.elim (id : M → M) b) ∘ Sum.map Subtype.val id) ∘
      Sum.map (fun i => (⟨a i, ⟨i, rfl⟩⟩ : Set.range a)) id) ↔ _ at h
  rw [he] at h
  exact h.symm

private noncomputable def unnameTuple {M : Type} {m n : ℕ} (a : Fin m → M)
    (φ : L[[Set.range a]].Formula (Fin n)) : L.Formula (Fin m ⊕ Fin n) :=
  Formula.relabel (Sum.map (fun x : Set.range a => Classical.choose x.property) id)
    (BoundedFormula.constantsVarsEquiv φ)

private theorem unnameTuple_realize {M : Type} [L.Structure M] {m n : ℕ}
    (a : Fin m → M) (φ : L[[Set.range a]].Formula (Fin n)) (b : Fin n → M) :
    (unnameTuple a φ).Realize (Sum.elim a b) ↔
      @Formula.Realize _ (NamedModel L M (Set.range a)) _ _ φ b := by
  rw [unnameTuple, Formula.realize_relabel]
  have h := parameterFormula_realize (ElementaryEmbedding.refl L M)
    (Set.range a) φ b
  rw [parameterFormula, Formula.realize_relabel] at h
  have he : Sum.elim a b ∘
      Sum.map (fun x : Set.range a => Classical.choose x.property) id =
      Sum.elim (fun x : Set.range a => (x : M)) b := by
    funext x
    cases x with
    | inl x => exact Classical.choose_spec x.property
    | inr i => rfl
  rw [he]
  have he' : Sum.elim (⇑(ElementaryEmbedding.refl L M)) b ∘ Sum.map Subtype.val id =
      Sum.elim (fun x : Set.range a => (x : M)) b := by
    funext x
    cases x <;> rfl
  rw [he'] at h
  exact h

theorem empty_tuple_isolated {M : Type} [L.Structure M] [Nonempty M] [M ⊨ T]
    (hT : T.IsComplete) :
    Isolates T (T.typeOf (Fin.elim0 : Fin 0 → M)) ⊤ := by
  apply (isolatesAt_iff _ _).mpr
  refine ⟨Formula.realize_top.mpr trivial, fun φ hφ => ?_⟩
  let σ := φ.relabel (Fin.elim0 : Fin 0 → Empty)
  have hσ : M ⊨ σ := by
    simpa only [σ, Sentence.Realize, Formula.realize_relabel,
      Subsingleton.elim (default ∘ Fin.elim0) Fin.elim0] using hφ
  have hmod := (hT.realize_sentence_iff σ M).mp hσ
  apply Theory.models_formula_iff.mpr
  intro N a
  change (⊤ : L.Formula (Fin 0)).Realize a → φ.Realize a
  intro _
  have hn := hmod.realize_sentence N
  simpa only [σ, Sentence.Realize, Formula.realize_relabel,
    Subsingleton.elim (default ∘ Fin.elim0) a] using hn

theorem joint_isolation {M : Type} [L.Structure M] [Nonempty M] [M ⊨ T]
    (_hT : T.IsComplete) {m n : ℕ} (a : Fin m → M) (b : Fin n → M) :
    Isolated T (T.typeOf (Fin.append a b)) ↔
      Isolated T (T.typeOf a) ∧ IsolatedOver (L := L) (Set.range a) b := by
  classical
  constructor
  · rintro ⟨θ, hθ⟩
    let δ : L.Formula (Fin m ⊕ Fin n) := θ.relabel finSumFinEquiv.symm
    have hδ : IsolatesAt T (Sum.elim a b) δ := by
      have h := reindex_isolatesAt finSumFinEquiv.symm (Fin.append a b) θ
        ((isolatesAt_iff _ _).mp hθ)
      simpa only [Equiv.symm_symm, sum_assignment] using h
    constructor
    · refine ⟨δ.iExs (Fin n), (isolatesAt_iff _ _).mpr ⟨?_, ?_⟩⟩
      · exact Formula.realize_iExs.mpr ⟨b, hδ.1⟩
      · intro ρ hρ
        have hρ' : (ρ.relabel Sum.inl).Realize (Sum.elim a b) := by
          simpa only [Formula.realize_relabel, Function.comp_def, Sum.elim_inl] using hρ
        apply Theory.models_formula_iff.mpr
        intro N x
        change (δ.iExs (Fin n)).Realize x → ρ.Realize x
        intro hx
        obtain ⟨y, hy⟩ := Formula.realize_iExs.mp hx
        have hr : (ρ.relabel Sum.inl).Realize (Sum.elim x y) :=
          (hδ.2 _ hρ').realize_formula N hy
        simpa only [Formula.realize_relabel, Function.comp_def, Sum.elim_inl] using hr
    · change ∃ χ, Isolates _ _ χ
      refine ⟨nameTuple a δ, (isolatesAt_iff (M := NamedModel L M (Set.range a))
        (fun i => b i) _).mpr ⟨?_, ?_⟩⟩
      · exact (nameTuple_realize a δ b).mpr hδ.1
      · intro φ hφ
        apply (complete_models_formula (M := NamedModel L M (Set.range a)) _).mpr
        intro y
        change (nameTuple a δ).Realize y → φ.Realize y
        intro hy
        have hφ' := (unnameTuple_realize a φ b).mpr hφ
        have hδy := (nameTuple_realize a δ y).mp hy
        exact (unnameTuple_realize a φ y).mp ((hδ.2 _ hφ').realize_formula M hδy)
  · rintro ⟨⟨ψ, hψ⟩, ⟨χ, hχ⟩⟩
    have hψ' := (isolatesAt_iff _ _).mp hψ
    have hχ' := (isolatesAt_iff (M := NamedModel L M (Set.range a))
      (T := L[[Set.range a]].completeTheory
      (NamedModel L M (Set.range a))) (fun i => (b i : NamedModel L M (Set.range a))) χ).mp hχ
    let δ : L.Formula (Fin m ⊕ Fin n) := ψ.relabel Sum.inl ⊓ unnameTuple a χ
    have hδ : IsolatesAt T (Sum.elim a b) δ := by
      refine ⟨Formula.realize_inf.mpr ⟨?_, ?_⟩, ?_⟩
      · simpa only [Formula.realize_relabel, Function.comp_def, Sum.elim_inl] using hψ'.1
      · exact (unnameTuple_realize a χ b).mpr hχ'.1
      · intro η hη
        let ρ : L.Formula (Fin m) := ((unnameTuple a χ).imp η).iAlls (Fin n)
        have hρ : ρ.Realize a := by
          apply Formula.realize_iAlls.mpr
          intro y
          change (unnameTuple a χ).Realize (Sum.elim a y) → η.Realize (Sum.elim a y)
          intro hχy
          have hη' := (nameTuple_realize a η b).mpr hη
          have hχN := (unnameTuple_realize a χ y).mp hχy
          exact (nameTuple_realize a η y).mp
            ((hχ'.2 _ hη').realize_formula (NamedModel L M (Set.range a)) hχN)
        apply Theory.models_formula_iff.mpr
        intro N v
        change δ.Realize v → η.Realize v
        intro hv
        obtain ⟨hψv, hχv⟩ := Formula.realize_inf.mp hv
        have hψx : ψ.Realize (v ∘ Sum.inl) := Formula.realize_relabel.mp hψv
        have hρx : ρ.Realize (v ∘ Sum.inl) := (hψ'.2 _ hρ).realize_formula N hψx
        have hy := Formula.realize_iAlls.mp hρx (v ∘ Sum.inr)
        have hsplit : Sum.elim (v ∘ Sum.inl) (v ∘ Sum.inr) = v := by
          funext i
          cases i <;> rfl
        rw [hsplit] at hy
        exact hy hχv
    have h := reindex_isolatesAt finSumFinEquiv (Sum.elim a b) δ hδ
    have he : Sum.elim a b ∘ finSumFinEquiv.symm = Fin.append a b := by
      funext i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp
    rw [he] at h
    exact ⟨δ.relabel finSumFinEquiv, (isolatesAt_iff _ _).mpr h⟩

theorem atomic_iff_finite_parameters {M : Type} [L.Structure M] [Nonempty M] [M ⊨ T]
    (hT : T.IsComplete) :
    IsAtomic T M ↔ ∀ (A : Set M), A.Finite →
      ∀ b : M, IsolatedOver (L := L) A (fun _ : Fin 1 => b) := by
  classical
  constructor
  · intro hM A hA b
    let : Finite A := hA.to_subtype
    let := Fintype.ofFinite A
    let m := Fintype.card A
    let e : A ≃ Fin m := Fintype.equivFin A
    let a : Fin m → M := Subtype.val ∘ e.symm
    have hrange : Set.range a = A := by
      ext x
      constructor
      · rintro ⟨i, rfl⟩
        exact (e.symm i).property
      · intro hx
        exact ⟨e ⟨x, hx⟩, congrArg Subtype.val (e.symm_apply_apply ⟨x, hx⟩)⟩
    have hparam := ((joint_isolation hT a (fun _ : Fin 1 => b)).mp
      (hM _ (Fin.append a (fun _ : Fin 1 => b)))).2
    simpa only [hrange] using hparam
  · intro h n
    induction n with
    | zero =>
        intro a
        have ha : a = (Fin.elim0 : Fin 0 → M) := Subsingleton.elim _ _
        rw [ha]
        exact ⟨⊤, empty_tuple_isolated hT⟩
    | succ n ih =>
        intro a
        let c := Fin.init a
        let b : Fin 1 → M := fun _ => a (Fin.last n)
        have hparam : IsolatedOver (L := L) (Set.range c) b :=
          h (Set.range c) (Set.finite_range c) (a (Fin.last n))
        have hjoint := (joint_isolation hT c b).mpr ⟨ih c, hparam⟩
        have he : Fin.append c b = a := by
          rw [Fin.append_right_eq_snoc]
          exact Fin.snoc_init_self a
        simpa only [he] using hjoint

end Lemmatheca.ModelTheory.AtomicAndPrimeModels
