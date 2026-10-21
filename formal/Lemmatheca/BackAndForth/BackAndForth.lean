import Lemmatheca.ElementarySubmodels.ElementarySubmodels
import Lemmatheca.FirstOrderStructures.FirstOrderSemantics
import Mathlib.ModelTheory.Order
import Mathlib.Order.Ideal

open Lemmatheca.MathematicalLogic

/-! Finite atomic partial maps and the countable back-and-forth theorem.
The domains below need not be substructures: atomic formulas include arbitrary terms.
-/

namespace Lemmatheca.ModelTheory.BackAndForth

open FirstOrder FirstOrder.Language

universe u v w w'

variable {L : Language.{u, v}} {M : Type w} {N : Type w'}
variable [L.Structure M] [L.Structure N]

/-- A finite partial isomorphism preserves every atomic formula on its domain.
Terms are evaluated in the ambient structures, not in the finite domain. -/
structure FinitePartialIso (L : Language.{u, v}) (M : Type w) (N : Type w')
    [L.Structure M] [L.Structure N] where
  dom : Set M
  finite_dom : dom.Finite
  toFun : dom → N
  injective : Function.Injective toFun
  atomic : ∀ {n} (φ : L.Formula (Fin n)), φ.IsAtomic → ∀ a : Fin n → dom,
    φ.Realize (toFun ∘ a) ↔ φ.Realize (Subtype.val ∘ a)

namespace FinitePartialIso

instance : LE (FinitePartialIso L M N) := ⟨fun p q =>
  ∃ h : p.dom ⊆ q.dom, ∀ a : p.dom, q.toFun ⟨a, h a.2⟩ = p.toFun a⟩

instance : Preorder (FinitePartialIso L M N) where
  le_refl p := ⟨Set.Subset.rfl, fun _ => rfl⟩
  le_trans p q r := by
    rintro ⟨hpq, heq⟩ ⟨hqr, heq'⟩
    exact ⟨hpq.trans hqr, fun a => (heq' ⟨a, hpq a.2⟩).trans (heq a)⟩

theorem dom_mono {p q : FinitePartialIso L M N} (h : p ≤ q) : p.dom ⊆ q.dom := h.1

theorem map_mono {p q : FinitePartialIso L M N} (h : p ≤ q) (a : p.dom) :
    q.toFun ⟨a, h.1 a.2⟩ = p.toFun a := h.2 a

/-- Atomic preservation extends through Boolean connectives. -/
theorem quantifierFree (p : FinitePartialIso L M N) {n : ℕ}
    (φ : L.Formula (Fin n)) (hφ : φ.IsQF) (a : Fin n → p.dom) :
    φ.Realize (p.toFun ∘ a) ↔ φ.Realize (Subtype.val ∘ a) := by
  induction hφ with
  | falsum => exact Iff.rfl
  | of_isAtomic h => exact p.atomic _ h a
  | imp _ _ h₁ h₂ => simp only [Formula.realize_imp, h₁, h₂]

/-- Disagreement on a closed atomic formula prevents even an empty partial map. -/
theorem closed_atomic_agreement (p : FinitePartialIso L M N)
    (φ : L.Formula (Fin 0)) (hφ : φ.IsAtomic) :
    φ.Realize (Fin.elim0 : Fin 0 → N) ↔ φ.Realize (Fin.elim0 : Fin 0 → M) := by
  have hN : p.toFun ∘ (Fin.elim0 : Fin 0 → p.dom) = (Fin.elim0 : Fin 0 → N) :=
    Subsingleton.elim _ _
  have hM : Subtype.val ∘ (Fin.elim0 : Fin 0 → p.dom) = (Fin.elim0 : Fin 0 → M) :=
    Subsingleton.elim _ _
  simpa only [hN, hM] using p.atomic φ hφ (Fin.elim0 : Fin 0 → p.dom)

/-- The union of an increasing sequence of partial isomorphisms covering both
carriers is an isomorphism, agreeing with every member of the sequence. -/
theorem chain_isomorphism (p : ℕ → FinitePartialIso L M N) (hp : Monotone p)
    (hdom : ∀ a : M, ∃ n, a ∈ (p n).dom)
    (hran : ∀ b : N, ∃ n, ∃ a : (p n).dom, (p n).toFun a = b) :
    ∃ e : M ≃[L] N, ∀ n (a : (p n).dom), e a = (p n).toFun a := by
  classical
  let stage (a : M) := Classical.choose (hdom a)
  have hstage (a : M) : a ∈ (p (stage a)).dom := Classical.choose_spec (hdom a)
  let f (a : M) := (p (stage a)).toFun ⟨a, hstage a⟩
  have hagree (n : ℕ) (a : (p n).dom) : f a = (p n).toFun a := by
    let k := max (stage a) n
    have h₁ := map_mono (hp (show stage a ≤ k from le_max_left _ _)) ⟨a, hstage a⟩
    have h₂ := map_mono (hp (show n ≤ k from le_max_right _ _)) a
    exact h₁.symm.trans h₂
  have htuple {n : ℕ} (a : Fin n → M) : ∃ k, ∀ i, a i ∈ (p k).dom := by
    let k := Finset.univ.sup (stage ∘ a)
    refine ⟨k, fun i => ?_⟩
    exact dom_mono (hp (Finset.le_sup (Finset.mem_univ i))) (hstage (a i))
  have hatomic {n : ℕ} (φ : L.Formula (Fin n)) (hφ : φ.IsAtomic) (a : Fin n → M) :
      φ.Realize (f ∘ a) ↔ φ.Realize a := by
    obtain ⟨k, hk⟩ := htuple a
    let a' : Fin n → (p k).dom := fun i => ⟨a i, hk i⟩
    have hmap : (p k).toFun ∘ a' = f ∘ a := by funext i; exact (hagree k (a' i)).symm
    have h := (p k).atomic φ hφ a'
    rw [hmap] at h
    exact h
  have hinj : Function.Injective f := by
    intro a b hab
    obtain ⟨k, hk⟩ := htuple (Fin.cons a (Fin.cons b Fin.elim0))
    have ha := hk 0
    have hb := hk 1
    have h := (p k).injective ((hagree k ⟨a, ha⟩).symm.trans (hab.trans (hagree k ⟨b, hb⟩)))
    exact congrArg Subtype.val h
  have hsurj : Function.Surjective f := by
    intro b
    obtain ⟨k, a, ha⟩ := hran b
    exact ⟨a, (hagree k a).trans ha⟩
  let e : M ≃ N := _root_.Equiv.ofBijective f ⟨hinj, hsurj⟩
  refine ⟨{ e with map_fun' := ?_, map_rel' := ?_ }, hagree⟩
  · intro n g a
    have h := (hatomic (Formula.graph g) (Formula.isAtomic_graph g)
      (Fin.cons (Structure.funMap g a) a)).mpr (Formula.realize_graph.mpr rfl)
    have heq : f ∘ Fin.cons (Structure.funMap g a) a =
        Fin.cons (f (Structure.funMap g a)) (f ∘ a) := Fin.comp_cons ..
    rw [heq, Formula.realize_graph] at h
    exact h.symm
  · intro n r a
    exact hatomic (.rel r (fun i => .var (.inl i))) (.rel r _) a

end FinitePartialIso

/-- A nonempty family of finite partial maps with extension in both directions. -/
structure BackForthSystem (L : Language.{u, v}) (M : Type w) (N : Type w')
    [L.Structure M] [L.Structure N] where
  maps : Set (FinitePartialIso L M N)
  nonempty : maps.Nonempty
  forth : ∀ p ∈ maps, ∀ a : M, ∃ q ∈ maps, p ≤ q ∧ a ∈ q.dom
  back : ∀ p ∈ maps, ∀ b : N, ∃ q ∈ maps, p ≤ q ∧ ∃ a : q.dom, q.toFun a = b

/-- For countable carriers, every map in a back-and-forth system extends to an
isomorphism. Countability of the language is not required. -/
theorem countable_isomorphism [Countable M] [Countable N]
    (S : BackForthSystem L M N) (p₀ : FinitePartialIso L M N) (hp₀ : p₀ ∈ S.maps) :
    ∃ e : M ≃[L] N, ∀ a : p₀.dom, e a = p₀.toFun a := by
  classical
  let P := S.maps
  let D : M ⊕ N → Order.Cofinal P := fun x => match x with
    | .inl a => {
        carrier := {p | a ∈ p.val.dom}
        isCofinal := by
          intro p
          obtain ⟨q, hq, hpq, ha⟩ := S.forth p p.2 a
          exact ⟨⟨q, hq⟩, ha, hpq⟩ }
    | .inr b => {
        carrier := {p | ∃ a : p.val.dom, p.val.toFun a = b}
        isCofinal := by
          intro p
          obtain ⟨q, hq, hpq, ha⟩ := S.back p p.2 b
          exact ⟨⟨q, hq⟩, ha, hpq⟩ }
  let : Encodable (M ⊕ N) := Encodable.ofCountable _
  let s := Order.sequenceOfCofinals (⟨p₀, hp₀⟩ : P) D
  have hs : Monotone (fun n => (s n).val) := by
    intro i j hij
    exact (show s i ≤ s j from Order.sequenceOfCofinals.monotone (⟨p₀, hp₀⟩ : P) D hij)
  have hdom (a : M) : ∃ n, a ∈ (s n).val.dom :=
    ⟨_, Order.sequenceOfCofinals.encode_mem (⟨p₀, hp₀⟩ : P) D (.inl a)⟩
  have hran (b : N) : ∃ n, ∃ a : (s n).val.dom, (s n).val.toFun a = b :=
    ⟨_, Order.sequenceOfCofinals.encode_mem (⟨p₀, hp₀⟩ : P) D (.inr b)⟩
  obtain ⟨e, he⟩ := FinitePartialIso.chain_isomorphism (fun n => (s n).val) hs hdom hran
  exact ⟨e, he 0⟩

section StrictOrders

open Lemmatheca.MathematicalLogic.FirstOrderSyntax
open Lemmatheca.MathematicalLogic.FirstOrderSemantics

variable {A : Type w} {B : Type w'} [LinearOrder A] [LinearOrder B]

local instance strictStructureA : binaryRelLanguage.Structure A :=
  binaryRelStructure A (fun a b => a < b)
local instance strictStructureB : binaryRelLanguage.Structure B :=
  binaryRelStructure B (fun a b => a < b)

/-- Order embeddings are embeddings of the actual strict-order language. -/
def strictOrderEmbedding (f : A ↪o B) : A ↪[binaryRelLanguage] B where
  toFun := f
  inj' := f.injective
  map_fun' := fun f => Empty.elim f
  map_rel' := by
    intro n r x
    cases r
    exact f.lt_iff_lt

/-- Turn a finite order embedding into the finite atomic partial map used here. -/
def ofOrderEmbedding (D : Set A) (hD : D.Finite) (f : D ↪o B) :
    FinitePartialIso binaryRelLanguage A B where
  dom := D
  finite_dom := hD
  toFun := f
  injective := f.injective
  atomic := by
    intro n φ hφ a
    let : binaryRelLanguage.Structure D := binaryRelStructure D (fun x y => x < y)
    have h₁ := hφ.isQF.realize_embedding (strictOrderEmbedding f) (v := a) (xs := default)
    have h₂ := hφ.isQF.realize_embedding (strictOrderEmbedding (OrderEmbedding.subtype D))
      (v := a) (xs := default)
    simp only [Formula.boundedFormula_realize_eq_realize] at h₁ h₂
    exact h₁.trans h₂.symm

/-- A finite partial isomorphism in this strict language is an order embedding. -/
theorem finitePartialIso_lt (p : FinitePartialIso binaryRelLanguage A B) (x y : p.dom) :
    p.toFun x < p.toFun y ↔ x < y := by
  let φ : binaryRelLanguage.Formula (Fin 2) :=
    .rel .rel ![.var (.inl 0), .var (.inl 1)]
  have h := p.atomic φ (.rel _ _) ![x, y]
  exact h

def toOrderEmbedding (p : FinitePartialIso binaryRelLanguage A B) : p.dom ↪o B :=
  OrderEmbedding.ofStrictMono p.toFun (fun x y hxy => (finitePartialIso_lt p x y).mpr hxy)

/-- Extend the very same finite atomic map by any prescribed source point. -/
theorem strict_forth [DenselyOrdered B] [NoMinOrder B] [NoMaxOrder B] [Nonempty B]
    (p : FinitePartialIso binaryRelLanguage A B) (a : A) :
    ∃ q : FinitePartialIso binaryRelLanguage A B, p ≤ q ∧ a ∈ q.dom := by
  classical
  let D := p.finite_dom.toFinset
  have hD : (D : Set A) = p.dom := p.finite_dom.coe_toFinset
  let f : D ↪o B := ((Set.orderIsoOfEq _ _ hD).toOrderEmbedding).trans (toOrderEmbedding p)
  obtain ⟨g, hg⟩ := Order.exists_orderEmbedding_insert D f a
  let q := ofOrderEmbedding (A := A) (B := B) (show Set A from ↑(insert a D : Finset A)) (Finset.finite_toSet _) g
  refine ⟨q, ⟨?_, ?_⟩, ?_⟩
  · intro x hx
    exact Finset.mem_insert.mpr (Or.inr (by simpa only [D, Set.Finite.mem_toFinset] using hx))
  · intro x
    have hx : (x : A) ∈ D := by simpa only [D, Set.Finite.mem_toFinset] using x.2
    exact congrFun hg ⟨x, hx⟩
  · exact Finset.mem_insert_self a D

noncomputable def rangeOrderIso (p : FinitePartialIso binaryRelLanguage A B) :
    p.dom ≃o Set.range p.toFun :=
  { _root_.Equiv.ofInjective p.toFun p.injective with
    map_rel_iff' := (toOrderEmbedding p).le_iff_le }

/-- Reverse the finite partial order isomorphism, without changing its graph. -/
noncomputable def orderSymm (p : FinitePartialIso binaryRelLanguage A B) :
    FinitePartialIso binaryRelLanguage B A := by
  let : Finite p.dom := p.finite_dom.to_subtype
  exact ofOrderEmbedding (Set.range p.toFun) (Set.finite_range _)
    ((rangeOrderIso p).symm.toOrderEmbedding.trans (OrderEmbedding.subtype p.dom))

theorem orderSymm_apply (p : FinitePartialIso binaryRelLanguage A B) (x : p.dom) :
    (orderSymm p).toFun ⟨p.toFun x, ⟨x, rfl⟩⟩ = (x : A) := by
  exact congrArg Subtype.val ((rangeOrderIso p).symm_apply_apply x)

/-- Extend the same finite atomic map by any prescribed target point. -/
theorem strict_back [DenselyOrdered A] [NoMinOrder A] [NoMaxOrder A] [Nonempty A]
    (p : FinitePartialIso binaryRelLanguage A B) (b : B) :
    ∃ q : FinitePartialIso binaryRelLanguage A B, p ≤ q ∧
      ∃ a : q.dom, q.toFun a = b := by
  classical
  obtain ⟨r, hr, hb⟩ := strict_forth (orderSymm p) b
  let q := orderSymm r
  have hrmap (x : p.dom) :
      r.toFun ⟨p.toFun x, hr.1 ⟨x, rfl⟩⟩ = (x : A) :=
    (hr.2 ⟨p.toFun x, ⟨x, rfl⟩⟩).trans (orderSymm_apply p x)
  have hdom : p.dom ⊆ q.dom := by
    intro x hx
    exact ⟨⟨p.toFun ⟨x, hx⟩, hr.1 ⟨⟨x, hx⟩, rfl⟩⟩, hrmap ⟨x, hx⟩⟩
  refine ⟨q, ⟨hdom, ?_⟩, ?_⟩
  · intro x
    have h := orderSymm_apply r ⟨p.toFun x, hr.1 ⟨x, rfl⟩⟩
    simpa only [hrmap x] using h
  · refine ⟨⟨r.toFun ⟨b, hb⟩, ⟨⟨b, hb⟩, rfl⟩⟩, ?_⟩
    exact orderSymm_apply r ⟨b, hb⟩

/-- The empty finite order map in the strict-order language. -/
def emptyStrictPartialIso : FinitePartialIso binaryRelLanguage A B :=
  ofOrderEmbedding ∅ Set.finite_empty
    (OrderEmbedding.ofStrictMono (fun x : (∅ : Set A) => False.elim x.2)
      (fun x => False.elim x.2))

/-- Finite maps from our actual atomic-map definition form a back-and-forth system
between any two nonempty dense linear orders without endpoints. -/
noncomputable def strictDenseOrderSystem
    [DenselyOrdered A] [NoMinOrder A] [NoMaxOrder A] [Nonempty A]
    [DenselyOrdered B] [NoMinOrder B] [NoMaxOrder B] [Nonempty B] :
    BackForthSystem binaryRelLanguage A B where
  maps := Set.univ
  nonempty := ⟨emptyStrictPartialIso, Set.mem_univ _⟩
  forth := by
    intro p _ a
    obtain ⟨q, hpq, ha⟩ := strict_forth p a
    exact ⟨q, Set.mem_univ _, hpq, ha⟩
  back := by
    intro p _ b
    obtain ⟨q, hpq, ha⟩ := strict_back p b
    exact ⟨q, Set.mem_univ _, hpq, ha⟩

/-- Every prescribed finite order match between countable dense linear orders
extends to an isomorphism in the same strict-order language. -/
theorem strict_countable_isomorphism
    [DenselyOrdered A] [NoMinOrder A] [NoMaxOrder A] [Nonempty A] [Countable A]
    [DenselyOrdered B] [NoMinOrder B] [NoMaxOrder B] [Nonempty B] [Countable B]
    (p : FinitePartialIso binaryRelLanguage A B) :
    ∃ e : A ≃[binaryRelLanguage] B, ∀ a : p.dom, e a = p.toFun a :=
  countable_isomorphism strictDenseOrderSystem p (Set.mem_univ _)

end StrictOrders

end Lemmatheca.ModelTheory.BackAndForth
