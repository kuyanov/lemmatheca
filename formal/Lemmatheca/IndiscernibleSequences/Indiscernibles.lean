import Lemmatheca.TypesAndRealization.Types
import Lemmatheca.PartitionRelations.PartitionRelations
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Finset.Sort

/-! Finite tuple selections, named parameters and locally based indiscernibility. -/
namespace Lemmatheca.ModelTheory.IndiscernibleSequences
open FirstOrder FirstOrder.Language

universe u v w w' z
variable {L : Language.{u, v}} {M : Type w} {N : Type w'}
variable {I : Type z} [LinearOrder I] {m n : ℕ}

/-- Flatten the selected blocks in block-major order, retaining every coordinate. -/
def tupleAssignment (a : I → Fin m → M) (s : Fin n → I) : Fin (n * m) → M :=
  fun x => let p : Fin n × Fin m := finProdFinEquiv.symm x
    a (s p.1) p.2

/-- Order indiscernibility in one specified language, with its existing constants fixed. -/
def OrderIndiscernibleIn (K : Language) {V : Type*} [K.Structure V]
    (a : I → Fin m → V) : Prop :=
  ∀ n, 0 < n → ∀ (φ : K.Formula (Fin (n * m))) (s t : Fin n ↪o I),
    φ.Realize (tupleAssignment a s) ↔ φ.Realize (tupleAssignment a t)

/-- Indiscernibility for all injective selections, without a restriction to their increasing order. -/
def SetIndiscernibleIn (K : Language) {V : Type*} [K.Structure V]
    (a : I → Fin m → V) : Prop :=
  ∀ n, 0 < n → ∀ (φ : K.Formula (Fin (n * m))) (s t : Fin n ↪ I),
    φ.Realize (tupleAssignment a s) ↔ φ.Realize (tupleAssignment a t)

variable [L.Structure M] [L.Structure N]

/-- The parameter names have their canonical values in the specified structure. -/
def OrderIndiscernible (A : Set M) (a : I → Fin m → M) : Prop :=
  OrderIndiscernibleIn L[[A]] a

def SetIndiscernible (A : Set M) (a : I → Fin m → M) : Prop :=
  SetIndiscernibleIn L[[A]] a

theorem setIndiscernible_orderIndiscernible {A : Set M} {a : I → Fin m → M}
    (h : SetIndiscernible (L := L) A a) : OrderIndiscernible (L := L) A a := by
  intro n hn φ s t
  exact h n hn φ s.toEmbedding t.toEmbedding

theorem constant_indiscernible (A : Set M) (a : Fin m → M) :
    OrderIndiscernible (L := L) A (fun _ : I => a) := by
  intro n hn φ s t
  rfl

/-- The equality is between actual complete types in the same finite variable context. -/
theorem orderIndiscernible_iff_types [Nonempty M] (A : Set M) (a : I → Fin m → M) :
    OrderIndiscernible (L := L) A a ↔
      ∀ n, 0 < n → ∀ (s t : Fin n ↪o I),
        (L[[A]].completeTheory M).typeOf (tupleAssignment a s) =
          (L[[A]].completeTheory M).typeOf (tupleAssignment a t) := by
  constructor
  · intro h n hn s t
    apply SetLike.ext
    intro γ
    simp only [Theory.CompleteType.mem_typeOf]
    exact h n hn (Formula.equivSentence.symm γ) s t
  · intro h n hn φ s t
    have he := h n hn s t
    have ht := congrArg (fun p => Formula.equivSentence φ ∈ p) he
    simpa only [Theory.CompleteType.formula_mem_typeOf] using Iff.of_eq ht

/-- Keep old parameter labels through this particular elementary map. -/
def LocallyBased (A : Set M) (f : M ↪ₑ[L] N) (source : ℕ → Fin m → M)
    (b : I → Fin m → N) : Prop :=
  ∀ n, 0 < n → ∀ (Δ : Finset (L[[A]].Formula (Fin (n * m)))) (s : Fin n ↪o I),
    ∃ t : Fin n ↪o ℕ, ∀ φ ∈ Δ,
      (@Formula.Realize _ (f.toEmbedding.withConstants A) _ _ φ (tupleAssignment b s) ↔
        φ.Realize (tupleAssignment source t))

/-- Naming the image parameter set agrees with retaining the source labels through the embedding. -/
theorem image_parameters_indiscernible (A : Set M) (f : M ↪ₑ[L] N) (b : I → Fin m → N) :
    OrderIndiscernible (L := L) (f '' A) b ↔
      OrderIndiscernibleIn (V := f.toEmbedding.withConstants A) L[[A]] b := by

  classical
  let e : A ≃ f '' A := Equiv.Set.image f A f.injective
  let : (constantsOn A).Structure N := constantsOn.structure (fun a : A => f a.val)
  let : L[[A]].Structure N := inferInstance
  let : (LHom.constantsOnMap (e : A → f '' A)).IsExpansionOn N :=
    constantsOnMap_isExpansionOn rfl
  let : (LHom.constantsOnMap (e.symm : f '' A → A)).IsExpansionOn N :=
    constantsOnMap_isExpansionOn (by
      funext x
      exact congrArg Subtype.val (e.apply_symm_apply x))
  let g := L.lhomWithConstantsMap (e : A → f '' A)
  let h := L.lhomWithConstantsMap (e.symm : f '' A → A)
  let : g.IsExpansionOn N := by
    constructor
    · intro n F x
      cases F with
      | inl F => rfl
      | inr F =>
        cases n with
        | zero => rfl
        | succ n => exact isEmptyElim F
    · intro n R x
      cases R with
      | inl R => rfl
      | inr R => exact isEmptyElim R
  let : h.IsExpansionOn N := by
    constructor
    · intro n F x
      cases F with
      | inl F => rfl
      | inr F =>
        cases n with
        | zero => exact congrArg Subtype.val (e.apply_symm_apply F)
        | succ n => exact isEmptyElim F
    · intro n R x
      cases R with
      | inl R => rfl
      | inr R => exact isEmptyElim R
  change OrderIndiscernibleIn L[[f '' A]] b ↔ OrderIndiscernibleIn L[[A]] b
  constructor
  · intro hi n hn φ s t
    exact (g.realize_onFormula φ).symm.trans ((hi n hn (g.onFormula φ) s t).trans
      (g.realize_onFormula φ))
  · intro hi n hn φ s t
    exact (h.realize_onFormula φ).symm.trans ((hi n hn (h.onFormula φ) s t).trans
      (h.realize_onFormula φ))

theorem locallyBased_preserves_uniform_test {A : Set M} {f : M ↪ₑ[L] N}
    {source : ℕ → Fin m → M} {b : I → Fin m → N}
    (h : LocallyBased A f source b) (hn : 0 < n)
    (φ : L[[A]].Formula (Fin (n * m))) (ε : Bool)
    (hφ : ∀ t : Fin n ↪o ℕ, φ.Realize (tupleAssignment source t) ↔ ε = true)
    (s : Fin n ↪o I) :
    @Formula.Realize _ (f.toEmbedding.withConstants A) _ _ φ (tupleAssignment b s) ↔
      ε = true := by
  classical
  obtain ⟨t, ht⟩ := h n hn {φ} s
  exact (ht φ (Finset.mem_singleton_self φ)).trans (hφ t)

theorem finite_formula_homogeneity (A : Set M) (source : ℕ → Fin m → M)
    (r : ℕ) (arities : Fin r → ℕ) (hn : ∀ j, 0 < arities j)
    (tests : ∀ j, Finset (L[[A]].Formula (Fin (arities j * m)))) :
    ∃ H : Set ℕ, H.Infinite ∧
      ∀ j (s t : Fin (arities j) ↪o ℕ),
        Set.range s ⊆ H → Set.range t ⊆ H →
        ∀ φ ∈ tests j,
          φ.Realize (tupleAssignment source s) ↔ φ.Realize (tupleAssignment source t) := by

  classical
  let k : Fin r → ℕ := fun j => Fintype.card (tests j → Bool)
  let E (j : Fin r) : (tests j → Bool) ≃ Fin (k j) := Fintype.equivFin _
  let c (j : Fin r) : Lemmatheca.SetTheory.PartitionRelations.Coloring ℕ (arities j) (Fin (k j)) :=
    fun S => E j (fun φ => decide (φ.val.Realize
      (tupleAssignment source (S.val.orderEmbOfFin S.property))))
  obtain ⟨H,hH,hhom⟩ := Lemmatheca.SetTheory.PartitionRelations.simultaneous_infinite_ramsey
    r arities k hn (fun _ => Fintype.card_pos) c
  refine ⟨H,hH,?_⟩
  intro j s t hs ht φ hφ
  let S : Lemmatheca.SetTheory.PartitionRelations.Subsets ℕ (arities j) :=
    ⟨Finset.univ.map s.toEmbedding,by simp⟩
  let T : Lemmatheca.SetTheory.PartitionRelations.Subsets ℕ (arities j) :=
    ⟨Finset.univ.map t.toEmbedding,by simp⟩
  have hS : (↑S.val : Set ℕ) ⊆ H := by
    intro x hx
    obtain ⟨i,_,rfl⟩ := Finset.mem_map.mp hx
    exact hs ⟨i,rfl⟩
  have hT : (↑T.val : Set ℕ) ⊆ H := by
    intro x hx
    obtain ⟨i,_,rfl⟩ := Finset.mem_map.mp hx
    exact ht ⟨i,rfl⟩
  have hsord : s = S.val.orderEmbOfFin S.property :=
    Finset.orderEmbOfFin_unique' _ (fun i => Finset.mem_map.mpr ⟨i,Finset.mem_univ _,rfl⟩)
  have htord : t = T.val.orderEmbOfFin T.property :=
    Finset.orderEmbOfFin_unique' _ (fun i => Finset.mem_map.mpr ⟨i,Finset.mem_univ _,rfl⟩)
  obtain ⟨color,hcolor⟩ := hhom j
  have he : c j S = c j T := (hcolor S hS).trans (hcolor T hT).symm
  have hv := congrFun ((E j).injective he) ⟨φ,hφ⟩
  change decide (φ.Realize (tupleAssignment source (S.val.orderEmbOfFin S.property))) =
    decide (φ.Realize (tupleAssignment source (T.val.orderEmbOfFin T.property))) at hv
  rw [← hsord,← htord] at hv
  have hh := congrArg (fun b : Bool => b = true) hv
  simpa only [decide_eq_true_eq] using Iff.of_eq hh


/-- The finite Boolean vectors actually witnessed by increasing source selections. -/
noncomputable def sourcePatterns (A : Set M) (source : ℕ → Fin m → M)
    (Δ : Finset (L[[A]].Formula (Fin (n * m)))) : Finset (Δ → Bool) := by
  classical
  exact Finset.univ.filter fun η => ∃ t : Fin n ↪o ℕ,
    (fun φ : Δ => decide (φ.val.Realize (tupleAssignment source t))) = η

/-- A disjunction over the actual source vectors, each specifying every selected formula. -/
noncomputable def patternFormula (A : Set M) (source : ℕ → Fin m → M)
    (Δ : Finset (L[[A]].Formula (Fin (n * m)))) :
    L[[A]].Formula (Fin (n * m)) := by
  classical
  exact (sourcePatterns A source Δ).toList.foldr (fun η θ =>
    (Δ.attach.toList.foldr (fun φ ψ => (if η φ then φ.val else φ.val.not) ⊓ ψ) ⊤) ⊔ θ) ⊥

theorem sourcePatterns_nonempty (A : Set M) (source : ℕ → Fin m → M)
    (Δ : Finset (L[[A]].Formula (Fin (n * m)))) :
    (sourcePatterns A source Δ).Nonempty := by
  classical
  let t : Fin n ↪o ℕ := Fin.valOrderEmb n
  refine ⟨(fun φ : Δ => decide (φ.val.Realize (tupleAssignment source t))), ?_⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, t, rfl⟩

theorem sourcePatterns_card_le (A : Set M) (source : ℕ → Fin m → M)
    (Δ : Finset (L[[A]].Formula (Fin (n * m)))) :
    (sourcePatterns A source Δ).card ≤ 2 ^ Δ.card := by
  classical
  calc
    (sourcePatterns A source Δ).card ≤ Fintype.card (Δ → Bool) := Finset.card_le_univ _
    _ = 2 ^ Δ.card := by simp

private theorem realize_inf_list {K : Language} {V : Type*} [K.Structure V] {α β : Type*}
    (l : List β) (F : β → K.Formula α) (b : α → V) :
    (l.foldr (fun x θ => F x ⊓ θ) ⊤).Realize b ↔
      ∀ x ∈ l, (F x).Realize b := by
  induction l with
  | nil => simp [Formula.Realize]
  | cons x l ih =>
      change ((F x ⊓ _).Realize b) ↔ _
      rw [Formula.Realize, BoundedFormula.realize_inf]
      change (F x).Realize b ∧ (l.foldr (fun x θ => F x ⊓ θ) ⊤).Realize b ↔ _
      rw [ih]
      simp only [List.mem_cons, forall_eq_or_imp]
private theorem realize_sup_list {K : Language} {V : Type*} [K.Structure V] {α β : Type*}
    (l : List β) (F : β → K.Formula α) (b : α → V) :
    (l.foldr (fun x θ => F x ⊔ θ) ⊥).Realize b ↔
      ∃ x ∈ l, (F x).Realize b := by
  induction l with
  | nil => simp [Formula.Realize]
  | cons x l ih =>
      change ((F x ⊔ _).Realize b) ↔ _
      rw [Formula.Realize, BoundedFormula.realize_sup]
      change (F x).Realize b ∨ (l.foldr (fun x θ => F x ⊔ θ) ⊥).Realize b ↔ _
      rw [ih]
      simp only [List.mem_cons, or_and_right, exists_or, exists_eq_left]


theorem patternFormula_realize (A : Set M) (source : ℕ → Fin m → M)
    (Δ : Finset (L[[A]].Formula (Fin (n * m)))) (f : M ↪ₑ[L] N)
    (b : Fin (n * m) → N) :
    @Formula.Realize _ (f.toEmbedding.withConstants A) _ _ (patternFormula A source Δ) b ↔
      ∃ t : Fin n ↪o ℕ, ∀ φ ∈ Δ,
        (@Formula.Realize _ (f.toEmbedding.withConstants A) _ _ φ b ↔
          φ.Realize (tupleAssignment source t)) := by
  classical
  let : L[[A]].Structure N := inferInstanceAs (L[[A]].Structure (f.toEmbedding.withConstants A))
  change (patternFormula A source Δ).Realize b ↔ _
  unfold patternFormula
  rw [realize_sup_list]
  simp only [Finset.mem_toList]
  constructor
  · rintro ⟨η, hη, hηb⟩
    obtain ⟨t, ht⟩ := (Finset.mem_filter.mp hη).2
    refine ⟨t, ?_⟩
    rw [realize_inf_list] at hηb
    intro φ hφ
    have hb := hηb ⟨φ,hφ⟩ (Finset.mem_toList.mpr (Finset.mem_attach _ _))
    have hs := congrFun ht ⟨φ,hφ⟩
    cases he : η ⟨φ,hφ⟩ with
    | false =>
        simp only [he, Bool.false_eq_true, ↓reduceIte, Formula.realize_not] at hb
        have hsource : ¬φ.Realize (tupleAssignment source t) := by simpa [he] using hs
        exact iff_of_false hb hsource
    | true =>
        simp only [he, ↓reduceIte] at hb
        have hsource : φ.Realize (tupleAssignment source t) := by simpa [he] using hs
        exact iff_of_true hb hsource
  · rintro ⟨t, ht⟩
    let η : Δ → Bool := fun φ => decide (φ.val.Realize (tupleAssignment source t))
    refine ⟨η, Finset.mem_filter.mpr ⟨Finset.mem_univ _, t, rfl⟩, ?_⟩
    rw [realize_inf_list]
    intro φ _
    have hb := ht φ.val φ.property
    cases he : η φ with
    | false =>
        simp only [Bool.false_eq_true, ↓reduceIte, Formula.realize_not]
        have hs : ¬φ.val.Realize (tupleAssignment source t) := by simpa [η] using he
        exact fun h => hs (hb.mp h)
    | true =>
        simp only [↓reduceIte]
        have hs : φ.val.Realize (tupleAssignment source t) := by simpa [η] using he
        exact hb.mpr hs

theorem patternFormula_empty (A : Set M) (source : ℕ → Fin m → M) :
    (∅ : L[[A]].Theory) ⊨ᵇ ((patternFormula (L := L) (n := n) A source ∅).iff ⊤) := by
  classical
  intro C b xs
  rw [BoundedFormula.realize_iff, BoundedFormula.realize_top]
  rw [Subsingleton.elim xs default]
  change (patternFormula (L := L) (n := n) A source ∅).Realize b ↔ True
  refine ⟨fun _ => trivial, fun _ => ?_⟩
  obtain ⟨η, hη⟩ := sourcePatterns_nonempty (L := L) (n := n) A source ∅
  unfold patternFormula
  rw [realize_sup_list]
  refine ⟨η, Finset.mem_toList.mpr hη, ?_⟩
  rw [realize_inf_list]
  simp

end Lemmatheca.ModelTheory.IndiscernibleSequences
