import Lemmatheca.BackAndForth.BackAndForth

/-! Finite elementary maps on arbitrary finite subsets of ambient structures.
This interface is shared by the atomic and saturated model constructions. -/

namespace Lemmatheca.ModelTheory.PartialElementaryMaps

open FirstOrder FirstOrder.Language

universe u v w w' z

variable {L : Language.{u, v}} {M : Type w} {N : Type w'}
variable [L.Structure M] [L.Structure N]

/-- Strengthen finite atomic partial isomorphisms to agreement on every formula. -/
structure FiniteMap (L : Language.{u, v}) (M : Type w) (N : Type w')
    [L.Structure M] [L.Structure N] extends BackAndForth.FinitePartialIso L M N where
  elementary : ∀ {n} (φ : L.Formula (Fin n)) (a : Fin n → dom),
    φ.Realize (toFun ∘ a) ↔ φ.Realize (Subtype.val ∘ a)

namespace FiniteMap

/-- The graph of the first map is contained in that of the second map. -/
def Extends (p q : FiniteMap L M N) : Prop :=
  p.toFinitePartialIso ≤ q.toFinitePartialIso

instance : LE (FiniteMap L M N) := ⟨Extends⟩

instance : Preorder (FiniteMap L M N) where
  le_refl p := le_refl p.toFinitePartialIso
  le_trans p q r := by
    intro hpq hqr
    change p.toFinitePartialIso ≤ r.toFinitePartialIso
    exact le_trans (show p.toFinitePartialIso ≤ q.toFinitePartialIso from hpq)
      (show q.toFinitePartialIso ≤ r.toFinitePartialIso from hqr)

theorem dom_mono {p q : FiniteMap L M N} (h : p ≤ q) : p.dom ⊆ q.dom := by
  exact h.1

theorem map_mono {p q : FiniteMap L M N} (h : p ≤ q) (a : p.dom) :
    q.toFun ⟨a, dom_mono h a.property⟩ = p.toFun a := by
  exact h.2 a

theorem underlying_le {p q : FiniteMap L M N} :
    p ≤ q ↔ p.toFinitePartialIso ≤ q.toFinitePartialIso := Iff.rfl

instance finiteDom (p : FiniteMap L M N) : Finite p.dom := p.finite_dom.to_subtype

def range (p : FiniteMap L M N) : Set N := Set.range p.toFun

theorem finite_range (p : FiniteMap L M N) : p.range.Finite := by
  exact Set.finite_range p.toFun

/-- The original function, regarded as a bijection onto its actual range. -/
noncomputable def rangeEquiv (p : FiniteMap L M N) : p.dom ≃ p.range :=
  Equiv.ofInjective p.toFun p.injective

/-- Reindexing gives agreement on every finite variable context. -/
theorem realize_finite (p : FiniteMap L M N) {α : Type z} [Finite α]
    (φ : L.Formula α) (a : α → p.dom) :
    φ.Realize (p.toFun ∘ a) ↔ φ.Realize (Subtype.val ∘ a) := by
  classical
  let := Fintype.ofFinite α
  let e := Fintype.equivFin α
  have h := p.elementary (φ.relabel e) (a ∘ e.symm)
  simpa only [Formula.realize_relabel, Function.comp_assoc, e.symm_comp_self,
    Function.comp_id] using h

private theorem tuple_agreement_aux {n : ℕ} (a : Fin n → M) (b : Fin n → N)
    (h : ∀ φ : L.Formula (Fin n), φ.Realize a ↔ φ.Realize b) {r : ℕ}
    (φ : L.Formula (Fin r)) (c : Fin r → Set.range a) :
    φ.Realize ((fun x : Set.range a => b (Classical.choose x.property)) ∘ c) ↔
      φ.Realize (Subtype.val ∘ c) := by
  let f : Fin r → Fin n := fun i => Classical.choose (c i).property
  have hf : a ∘ f = Subtype.val ∘ c := by
    funext i
    exact Classical.choose_spec (c i).property
  have hh := h (φ.relabel f)
  rw [Formula.realize_relabel, Formula.realize_relabel, hf] at hh
  exact hh.symm

private theorem tuple_injective_aux {n : ℕ} (a : Fin n → M) (b : Fin n → N)
    (h : ∀ φ : L.Formula (Fin n), φ.Realize a ↔ φ.Realize b) :
    Function.Injective (fun x : Set.range a => b (Classical.choose x.property)) := by
  intro x y hxy
  let i := Classical.choose x.property
  let j := Classical.choose y.property
  have hi : a i = x := Classical.choose_spec x.property
  have hj : a j = y := Classical.choose_spec y.property
  have heq := h ((Term.var i).equal (Term.var j))
  simp only [Formula.realize_equal, Term.realize_var] at heq
  exact Subtype.ext (hi.symm.trans ((heq.mpr hxy).trans hj))

/-- Choose preimages in the source tuple; equalities make the output independent
of that choice and ensure injectivity. -/
noncomputable def ofTuple {n : ℕ} (a : Fin n → M) (b : Fin n → N)
    (h : ∀ φ : L.Formula (Fin n), φ.Realize a ↔ φ.Realize b) : FiniteMap L M N where
  dom := Set.range a
  finite_dom := Set.finite_range a
  toFun := fun x => b (Classical.choose x.property)
  injective := tuple_injective_aux a b h
  atomic := fun φ _ c => tuple_agreement_aux a b h φ c
  elementary := tuple_agreement_aux a b h

theorem ofTuple_dom {n : ℕ} (a : Fin n → M) (b : Fin n → N)
    (h : ∀ φ : L.Formula (Fin n), φ.Realize a ↔ φ.Realize b) :
    (ofTuple a b h).dom = Set.range a := rfl

theorem ofTuple_apply {n : ℕ} (a : Fin n → M) (b : Fin n → N)
    (h : ∀ φ : L.Formula (Fin n), φ.Realize a ↔ φ.Realize b) (i : Fin n) :
    (ofTuple a b h).toFun ⟨a i, ⟨i, rfl⟩⟩ = b i := by
  let j := Classical.choose (show a i ∈ Set.range a from ⟨i, rfl⟩)
  have hj : a j = a i := Classical.choose_spec (show a i ∈ Set.range a from ⟨i, rfl⟩)
  have heq := h ((Term.var j).equal (Term.var i))
  simp only [Formula.realize_equal, Term.realize_var] at heq
  exact heq.mp hj

theorem ofTuple_range {n : ℕ} (a : Fin n → M) (b : Fin n → N)
    (h : ∀ φ : L.Formula (Fin n), φ.Realize a ↔ φ.Realize b) :
    (ofTuple a b h).range = Set.range b := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨Classical.choose x.property, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨⟨a i, ⟨i, rfl⟩⟩, ofTuple_apply a b h i⟩

theorem tuple_map_iff {n : ℕ} (a : Fin n → M) (b : Fin n → N) :
    (∀ φ : L.Formula (Fin n), φ.Realize a ↔ φ.Realize b) ↔
      ∃ p : FiniteMap L M N, p.dom = Set.range a ∧ p.range = Set.range b ∧
        ∀ i, ∃ ha : a i ∈ p.dom, p.toFun ⟨a i, ha⟩ = b i := by
  constructor
  · intro h
    exact ⟨ofTuple a b h, rfl, ofTuple_range a b h,
      fun i => ⟨⟨i, rfl⟩, ofTuple_apply a b h i⟩⟩
  · rintro ⟨p, hdom, _, hcoord⟩ φ
    let c : Fin n → p.dom := fun i => ⟨a i, hdom.symm ▸ Set.mem_range_self i⟩
    have hb : p.toFun ∘ c = b := by
      funext i
      obtain ⟨hi, hbi⟩ := hcoord i
      exact hbi
    have h := p.elementary φ c
    rw [hb] at h
    exact h.symm

private theorem zero_agreement (h : M ≅[L] N) (φ : L.Formula (Fin 0)) :
    φ.Realize (Fin.elim0 : Fin 0 → M) ↔ φ.Realize (Fin.elim0 : Fin 0 → N) := by
  let σ : L.Sentence := φ.relabel (Fin.elim0 : Fin 0 → Empty)
  have hh := h.realize_sentence σ
  change (φ.relabel _).Realize (default : Empty → M) ↔
    (φ.relabel _).Realize (default : Empty → N) at hh
  rw [Formula.realize_relabel, Formula.realize_relabel] at hh
  have hM : (default : Empty → M) ∘ (Fin.elim0 : Fin 0 → Empty) = Fin.elim0 :=
    Subsingleton.elim _ _
  have hN : (default : Empty → N) ∘ (Fin.elim0 : Fin 0 → Empty) = Fin.elim0 :=
    Subsingleton.elim _ _
  simpa only [hM, hN] using hh

/-- The actual empty map, under the necessary sentence-agreement hypothesis. -/
noncomputable def empty (h : M ≅[L] N) : FiniteMap L M N :=
  ofTuple (Fin.elim0 : Fin 0 → M) (Fin.elim0 : Fin 0 → N) (zero_agreement h)

theorem empty_dom (h : M ≅[L] N) : (empty h).dom = ∅ := by
  ext x
  simp only [empty, ofTuple_dom, Set.mem_range, IsEmpty.exists_iff,
    Set.notMem_empty]

theorem elementarilyEquivalent (p : FiniteMap L M N) : M ≅[L] N := by
  apply elementarilyEquivalent_iff.mpr
  intro σ
  have h := p.elementary (σ.relabel (Empty.elim : Empty → Fin 0))
    (Fin.elim0 : Fin 0 → p.dom)
  rw [Formula.realize_relabel, Formula.realize_relabel] at h
  have hM : (Subtype.val ∘ (Fin.elim0 : Fin 0 → p.dom)) ∘ Empty.elim =
      (default : Empty → M) := Subsingleton.elim _ _
  have hN : (p.toFun ∘ (Fin.elim0 : Fin 0 → p.dom)) ∘ Empty.elim =
      (default : Empty → N) := Subsingleton.elim _ _
  simpa only [hM, hN, Sentence.Realize] using h.symm

private theorem inverse_agreement (p : FiniteMap L M N) {n : ℕ}
    (φ : L.Formula (Fin n)) (a : Fin n → p.range) :
    φ.Realize ((fun b : p.range => (p.rangeEquiv.symm b : M)) ∘ a) ↔
      φ.Realize (Subtype.val ∘ a) := by
  have h := p.elementary φ (p.rangeEquiv.symm ∘ a)
  have heq : p.toFun ∘ (p.rangeEquiv.symm ∘ a) = Subtype.val ∘ a := by
    funext i
    exact congrArg Subtype.val (p.rangeEquiv.apply_symm_apply (a i))
  rw [heq] at h
  exact h.symm

/-- Reverse the actual range bijection. The domain is the original finite range. -/
noncomputable def symm (p : FiniteMap L M N) : FiniteMap L N M where
  dom := p.range
  finite_dom := p.finite_range
  toFun := fun b => (p.rangeEquiv.symm b : M)
  injective := Subtype.val_injective.comp p.rangeEquiv.symm.injective
  atomic := fun φ _ a => inverse_agreement p φ a
  elementary := inverse_agreement p

theorem symm_dom (p : FiniteMap L M N) : p.symm.dom = p.range := rfl

theorem symm_apply (p : FiniteMap L M N) (a : p.dom) :
    p.symm.toFun (p.rangeEquiv a) = (a : M) := by
  exact congrArg Subtype.val (p.rangeEquiv.symm_apply_apply a)

theorem symm_range (p : FiniteMap L M N) : p.symm.range = p.dom := by
  ext x
  constructor
  · rintro ⟨b, rfl⟩
    exact (p.rangeEquiv.symm b).property
  · intro hx
    exact ⟨p.rangeEquiv ⟨x, hx⟩, symm_apply p ⟨x, hx⟩⟩

private theorem ext_map {p q : FiniteMap L M N} (hdom : p.dom = q.dom)
    (hf : ∀ a : p.dom, q.toFun ⟨a, hdom ▸ a.property⟩ = p.toFun a) : p = q := by
  rcases p with ⟨⟨A, hA, f, hfi, hfa⟩, hfe⟩
  rcases q with ⟨⟨B, hB, g, hgi, hga⟩, hge⟩
  dsimp only at hdom
  subst B
  have hfun : g = f := funext hf
  subst g
  rfl

theorem symm_symm (p : FiniteMap L M N) : p.symm.symm = p := by
  apply ext_map (symm_range p)
  intro a
  let x : p.dom := ⟨a, symm_range p ▸ a.property⟩
  change p.toFun x = (p.symm.rangeEquiv.symm a : N)
  have hi := congrArg Subtype.val (p.symm.rangeEquiv.apply_symm_apply a)
  exact congrArg Subtype.val (p.symm.injective ((symm_apply p x).trans hi.symm))

theorem symm_le_symm {p q : FiniteMap L M N} (h : p ≤ q) : p.symm ≤ q.symm := by
  have hr : p.range ⊆ q.range := by
    rintro b ⟨a, rfl⟩
    exact ⟨⟨a, dom_mono h a.property⟩, map_mono h a⟩
  refine ⟨hr, ?_⟩
  intro b
  let a := p.rangeEquiv.symm b
  let a' : q.dom := ⟨a, dom_mono h a.property⟩
  have hpb : p.toFun a = (b : N) := congrArg Subtype.val (p.rangeEquiv.apply_symm_apply b)
  have hqb : q.toFun a' = (b : N) := (map_mono h a).trans hpb
  have heq : (⟨(b : N), hr b.property⟩ : q.range) = q.rangeEquiv a' :=
    Subtype.ext hqb.symm
  change q.symm.toFun ⟨(b : N), hr b.property⟩ = (a : M)
  exact (congrArg (fun z : q.range => q.symm.toFun z) heq).trans (symm_apply q a')

/-- Restrict the function to a supplied subset of its domain. -/
def restrict (p : FiniteMap L M N) (S : Set M) (h : S ⊆ p.dom) : FiniteMap L M N where
  dom := S
  finite_dom := p.finite_dom.subset h
  toFun := fun a => p.toFun ⟨a, h a.property⟩
  injective := by
    intro a b hab
    have heq : (⟨a, h a.property⟩ : p.dom) = ⟨b, h b.property⟩ := p.injective hab
    exact Subtype.ext (congrArg (fun x : p.dom => (x : M)) heq)
  atomic := fun φ hφ a => p.atomic φ hφ (fun i => ⟨a i, h (a i).property⟩)
  elementary := fun φ a => p.elementary φ (fun i => ⟨a i, h (a i).property⟩)

theorem restrict_dom (p : FiniteMap L M N) (S : Set M) (h : S ⊆ p.dom) :
    (p.restrict S h).dom = S := rfl

theorem restrict_apply (p : FiniteMap L M N) (S : Set M) (h : S ⊆ p.dom) (a : S) :
    (p.restrict S h).toFun a = p.toFun ⟨a, h a.property⟩ := rfl

theorem restrict_le (p : FiniteMap L M N) (S : Set M) (h : S ⊆ p.dom) :
    p.restrict S h ≤ p := by
  exact ⟨h, fun _ => rfl⟩

/-- A covering compatible sequence produces the specified elementary union map. -/
theorem chain_embedding (p : ℕ → FiniteMap L M N) (hp : Monotone p)
    (hdom : ∀ a : M, ∃ n, a ∈ (p n).dom) :
    ∃ e : M ↪ₑ[L] N, ∀ n (a : (p n).dom), e a = (p n).toFun a := by
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
  refine ⟨{ toFun := f, map_formula' := ?_ }, hagree⟩
  intro n φ a
  obtain ⟨k, hk⟩ := htuple a
  let a' : Fin n → (p k).dom := fun i => ⟨a i, hk i⟩
  have heq : (p k).toFun ∘ a' = f ∘ a := by
    funext i
    exact (hagree k (a' i)).symm
  have h := (p k).elementary φ a'
  rw [heq] at h
  exact h

/-- Answer the countably many domain requests, retaining every initial value. -/
theorem countable_embedding [Countable M]
    (forth : ∀ p : FiniteMap L M N, ∀ a : M,
      ∃ q : FiniteMap L M N, p ≤ q ∧ a ∈ q.dom) (p₀ : FiniteMap L M N) :
    ∃ e : M ↪ₑ[L] N, ∀ a : p₀.dom, e a = p₀.toFun a := by
  classical
  let D : M → Order.Cofinal (FiniteMap L M N) := fun a => {
    carrier := {p | a ∈ p.dom}
    isCofinal := by
      intro p
      obtain ⟨q, hpq, ha⟩ := forth p a
      exact ⟨q, ha, hpq⟩ }
  let : Encodable M := Encodable.ofCountable M
  let s := Order.sequenceOfCofinals p₀ D
  obtain ⟨e, he⟩ := chain_embedding s (Order.sequenceOfCofinals.monotone p₀ D)
    (fun a => ⟨_, Order.sequenceOfCofinals.encode_mem p₀ D a⟩)
  exact ⟨e, he 0⟩

end FiniteMap

end Lemmatheca.ModelTheory.PartialElementaryMaps
