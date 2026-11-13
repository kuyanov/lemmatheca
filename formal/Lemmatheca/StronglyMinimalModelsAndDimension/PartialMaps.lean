import Lemmatheca.AtomicAndPrimeModels.PartialElementaryMaps
import Mathlib.Order.Zorn

namespace Lemmatheca.ModelTheory.PartialElementaryMaps
open FirstOrder FirstOrder.Language
universe u v w w' z
noncomputable section
local instance smdPartialMapsPropDecidable : DecidablePred (fun p : Prop => p) := Classical.propDecidable
variable {L : Language.{u,v}} {M : Type w} {N : Type w'}
variable [L.Structure M] [L.Structure N]

/-- Elementary maps on actual subsets, without a finiteness restriction. -/
structure Map (L : Language.{u,v}) (M : Type w) (N : Type w')
    [L.Structure M] [L.Structure N] where
  dom : Set M
  toFun : dom → N
  injective : Function.Injective toFun
  elementary : ∀ {n : ℕ} (φ : L.Formula (Fin n)) (a : Fin n → dom),
    φ.Realize (toFun ∘ a) ↔ φ.Realize (Subtype.val ∘ a)

namespace Map

def range (p : Map L M N) : Set N := Set.range p.toFun

def rangeEquiv (p : Map L M N) : p.dom ≃ p.range := Equiv.ofInjective p.toFun p.injective

def ofFinite (p : FiniteMap L M N) : Map L M N where
  dom := p.dom
  toFun := p.toFun
  injective := p.injective
  elementary := p.elementary

def toFinite (p : Map L M N) (hfin : p.dom.Finite) : FiniteMap L M N where
  dom := p.dom
  finite_dom := hfin
  toFun := p.toFun
  injective := p.injective
  atomic := fun φ _ a => p.elementary φ a
  elementary := p.elementary

theorem realize_finite (p : Map L M N) {α : Type z} [Finite α]
    (φ : L.Formula α) (a : α → p.dom) :
    φ.Realize (p.toFun ∘ a) ↔ φ.Realize (Subtype.val ∘ a) := by
  classical
  let := Fintype.ofFinite α
  let e := Fintype.equivFin α
  have h := p.elementary (φ.relabel e) (a ∘ e.symm)
  simpa only [Formula.realize_relabel, Function.comp_assoc, e.symm_comp_self,
    Function.comp_id] using h

/-- Finite free-variable support connects arbitrary parameter indices to tuple elementarity. -/
theorem realize_formula (p : Map L M N) {α : Type z}
    (φ : L.Formula α) (a : α → p.dom) :
    φ.Realize (p.toFun ∘ a) ↔ φ.Realize (Subtype.val ∘ a) := by
  classical
  have h := p.realize_finite (φ.restrictFreeVar id) (a ∘ Subtype.val)
  change (φ.restrictFreeVar id).Realize (p.toFun ∘ (a ∘ Subtype.val)) default ↔
    (φ.restrictFreeVar id).Realize (Subtype.val ∘ (a ∘ Subtype.val)) default at h
  have hN : (φ.restrictFreeVar id).Realize (p.toFun ∘ (a ∘ Subtype.val)) default ↔
      BoundedFormula.Realize φ (p.toFun ∘ a) default :=
    BoundedFormula.realize_restrictFreeVar (p.toFun ∘ a) (fun _ => rfl)
  have hM : (φ.restrictFreeVar id).Realize (Subtype.val ∘ (a ∘ Subtype.val)) default ↔
      BoundedFormula.Realize φ (Subtype.val ∘ a) default :=
    BoundedFormula.realize_restrictFreeVar (Subtype.val ∘ a) (fun _ => rfl)
  exact hN.symm.trans (h.trans hM)

def empty (h : M ≅[L] N) : Map L M N := ofFinite (FiniteMap.empty h)

def restrict (p : Map L M N) (A : Set M) (hA : A ⊆ p.dom) : Map L M N where
  dom := A
  toFun := fun a => p.toFun ⟨a.val,hA a.property⟩
  injective := by
    intro a b he
    exact Subtype.ext (congrArg (fun x : p.dom => x.val) (p.injective he))
  elementary := fun φ a => p.elementary φ (fun i => ⟨(a i).val,hA (a i).property⟩)

def symm (p : Map L M N) : Map L N M where
  dom := p.range
  toFun := fun b => (p.rangeEquiv.symm b).val
  injective := Subtype.val_injective.comp p.rangeEquiv.symm.injective
  elementary := by
    intro n φ a
    have h := p.elementary φ (p.rangeEquiv.symm ∘ a)
    have heq : p.toFun ∘ (p.rangeEquiv.symm ∘ a) = Subtype.val ∘ a := by
      funext i
      exact congrArg Subtype.val (p.rangeEquiv.apply_symm_apply (a i))
    rw [heq] at h
    exact h.symm

theorem symm_apply (p : Map L M N) (a : p.dom) :
    p.symm.toFun (p.rangeEquiv a) = a.val := by
  exact congrArg Subtype.val (p.rangeEquiv.symm_apply_apply a)

theorem symm_range (p : Map L M N) : p.symm.range = p.dom := by
  ext x
  constructor
  · rintro ⟨b, rfl⟩
    exact (p.rangeEquiv.symm b).property
  · intro hx
    exact ⟨p.rangeEquiv ⟨x, hx⟩, symm_apply p ⟨x, hx⟩⟩

def graph (p : Map L M N) : Set (M × N) :=
  {xy | ∃ h : xy.1 ∈ p.dom, p.toFun ⟨xy.1,h⟩ = xy.2}

private theorem graph_symm (p : Map L M N) (xy : N × M) :
    xy ∈ graph p.symm ↔ (xy.2, xy.1) ∈ graph p := by
  constructor
  · rintro ⟨hb, he⟩
    let a := p.rangeEquiv.symm ⟨xy.1, hb⟩
    have ha : a.val = xy.2 := he
    have hf : p.toFun a = xy.1 :=
      congrArg Subtype.val (p.rangeEquiv.apply_symm_apply ⟨xy.1, hb⟩)
    rw [← ha]
    exact ⟨a.property, hf⟩
  · rintro ⟨ha, he⟩
    have hb : xy.1 ∈ p.range := ⟨⟨xy.2, ha⟩, he⟩
    refine ⟨hb, ?_⟩
    have harg : (⟨xy.1, hb⟩ : p.range) = p.rangeEquiv ⟨xy.2, ha⟩ := Subtype.ext he.symm
    change (p.rangeEquiv.symm (⟨xy.1, hb⟩ : p.range)).val = xy.2
    rw [harg]
    exact congrArg Subtype.val (p.rangeEquiv.symm_apply_apply ⟨xy.2, ha⟩)

theorem graph_injective : Function.Injective (graph (L := L) (M := M) (N := N)) := by
  intro p q h
  rcases p with ⟨A, f, hfi, hfe⟩
  rcases q with ⟨B, g, hgi, hge⟩
  have hAB : A = B := by
    ext x
    constructor
    · intro hx
      have hm : (x, f ⟨x, hx⟩) ∈ graph ⟨A, f, hfi, hfe⟩ := ⟨hx, rfl⟩
      rw [h] at hm
      exact hm.choose
    · intro hx
      have hm : (x, g ⟨x, hx⟩) ∈ graph ⟨B, g, hgi, hge⟩ := ⟨hx, rfl⟩
      rw [← h] at hm
      exact hm.choose
  subst B
  have hgf : g = f := by
    funext a
    have hm : (a.val, f a) ∈ graph ⟨A, f, hfi, hfe⟩ := ⟨a.property, rfl⟩
    rw [h] at hm
    exact hm.choose_spec
  subst g
  rfl

instance mapOrder : PartialOrder (Map L M N) := PartialOrder.lift graph graph_injective

theorem dom_mono {p q : Map L M N} (h : p ≤ q) : p.dom ⊆ q.dom := by
  intro x hx
  have hm : (x, p.toFun ⟨x, hx⟩) ∈ graph p := ⟨hx, rfl⟩
  exact (h hm).choose

theorem apply_mono {p q : Map L M N} (h : p ≤ q) (a : p.dom) :
    q.toFun ⟨a.val,dom_mono h a.property⟩ = p.toFun a := by
  have hm : (a.val, p.toFun a) ∈ graph p := ⟨a.property, rfl⟩
  exact (h hm).choose_spec

theorem range_mono {p q : Map L M N} (h : p ≤ q) : p.range ⊆ q.range := by
  rintro b ⟨a, rfl⟩
  exact ⟨⟨a.val, dom_mono h a.property⟩, apply_mono h a⟩

theorem symm_mono {p q : Map L M N} (h : p ≤ q) : p.symm ≤ q.symm := by
  intro xy hxy
  apply (graph_symm q xy).mpr
  exact h ((graph_symm p xy).mp hxy)

theorem restrict_le (p : Map L M N) (A : Set M) (hA : A ⊆ p.dom) :
    p.restrict A hA ≤ p := by
  rintro xy ⟨hx, hy⟩
  exact ⟨hA hx, hy⟩

private def chainValue (C : Set (Map L M N)) (a : ↥(⋃ p : C, p.val.dom)) : N :=
  let hex := Set.mem_iUnion.mp a.property
  let p : C := hex.choose
  p.val.toFun ⟨a.val, hex.choose_spec⟩

private theorem chain_value_eq (C : Set (Map L M N)) (hC : IsChain (· ≤ ·) C)
    (p : C) (a : ↥(⋃ q : C, q.val.dom)) (ha : a.val ∈ p.val.dom) :
    chainValue C a = p.val.toFun ⟨a.val, ha⟩ := by
  let hex := Set.mem_iUnion.mp a.property
  let q : C := hex.choose
  have hq : a.val ∈ q.val.dom := hex.choose_spec
  change q.val.toFun ⟨a.val, hq⟩ = p.val.toFun ⟨a.val, ha⟩
  rcases hC.total q.property p.property with hqp | hpq
  · exact (apply_mono hqp ⟨a.val, hq⟩).symm
  · exact apply_mono hpq ⟨a.val, ha⟩

private theorem chain_tuple (C : Set (Map L M N)) (hC : IsChain (· ≤ ·) C)
    (hne : C.Nonempty) {n : ℕ} (a : Fin n → ↥(⋃ q : C, q.val.dom)) :
    ∃ p : C, ∀ i, (a i).val ∈ p.val.dom := by
  induction n with
  | zero =>
      obtain ⟨p, hp⟩ := hne
      exact ⟨⟨p, hp⟩, fun i => Fin.elim0 i⟩
  | succ n ih =>
      obtain ⟨p, hp⟩ := ih (fun i => a i.succ)
      obtain ⟨q, hq⟩ := Set.mem_iUnion.mp (a 0).property
      rcases hC.total p.property q.property with hpq | hqp
      · refine ⟨q, ?_⟩
        intro i
        exact Fin.cases hq (fun j => dom_mono hpq (hp j)) i
      · refine ⟨p, ?_⟩
        intro i
        exact Fin.cases (dom_mono hqp hq) (fun j => hp j) i

/-- Union of the actual functions in a nonempty extension chain. -/
def chainUnion (C : Set (Map L M N)) (hC : IsChain (· ≤ ·) C) (hne : C.Nonempty) : Map L M N where
  dom := ⋃ p : C, p.val.dom
  toFun := fun a =>
    let hex := Set.mem_iUnion.mp a.property
    let p : C := hex.choose
    p.val.toFun ⟨a.val,hex.choose_spec⟩
  injective := by
    intro a b hab
    obtain ⟨p, hp⟩ := chain_tuple C hC hne (![a, b] : Fin 2 → ↥(⋃ q : C, q.val.dom))
    have ha : a.val ∈ p.val.dom := hp 0
    have hb : b.val ∈ p.val.dom := hp 1
    change chainValue C a = chainValue C b at hab
    have he : p.val.toFun ⟨a.val, ha⟩ = p.val.toFun ⟨b.val, hb⟩ :=
      (chain_value_eq C hC p a ha).symm.trans (hab.trans (chain_value_eq C hC p b hb))
    exact Subtype.ext (congrArg (fun x : p.val.dom => x.val) (p.val.injective he))
  elementary := by
    intro n φ a
    obtain ⟨p, hp⟩ := chain_tuple C hC hne a
    let b : Fin n → p.val.dom := fun i => ⟨(a i).val, hp i⟩
    have he : chainValue C ∘ a = p.val.toFun ∘ b := by
      funext i
      exact chain_value_eq C hC p (a i) (hp i)
    change φ.Realize (chainValue C ∘ a) ↔ φ.Realize (Subtype.val ∘ a)
    rw [he]
    exact p.val.elementary φ b

theorem chain_union_spec (C : Set (Map L M N)) (hC : IsChain (· ≤ ·) C) (hne : C.Nonempty) :
    (chainUnion C hC hne).dom = ⋃ p : C, p.val.dom ∧
      (chainUnion C hC hne).range = ⋃ p : C, p.val.range ∧
      ∀ p ∈ C, p ≤ chainUnion C hC hne := by
  have hext : ∀ p ∈ C, p ≤ chainUnion C hC hne := by
    intro p hp xy hxy
    obtain ⟨hx, hy⟩ := hxy
    have ha : xy.1 ∈ ⋃ q : C, q.val.dom := Set.mem_iUnion.mpr ⟨⟨p, hp⟩, hx⟩
    refine ⟨ha, ?_⟩
    exact (chain_value_eq C hC ⟨p, hp⟩ ⟨xy.1, ha⟩ hx).trans hy
  refine ⟨rfl, ?_, hext⟩
  ext b
  constructor
  · rintro ⟨a, rfl⟩
    obtain ⟨p, hp⟩ := Set.mem_iUnion.mp a.property
    apply Set.mem_iUnion.mpr
    refine ⟨p, ⟨⟨a.val, hp⟩, ?_⟩⟩
    exact (chain_value_eq C hC p a hp).symm
  · intro hb
    obtain ⟨p, hp⟩ := Set.mem_iUnion.mp hb
    exact range_mono (hext p.val p.property) hp

theorem exists_maximal_extension (p : Map L M N) :
    ∃ q : Map L M N, p ≤ q ∧ ∀ r : Map L M N, q ≤ r → r = q := by
  obtain ⟨q, hpq, hmax⟩ := zorn_le_nonempty_Ici₀ p
    (fun C _ hC c hc => ⟨chainUnion C hC ⟨c, hc⟩,
      fun r hr => (chain_union_spec C hC ⟨c, hc⟩).2.2 r hr⟩) p le_rfl
  exact ⟨q, hpq, fun r hqr => le_antisymm (hmax hqr) hqr⟩

theorem total_isomorphism (p : Map L M N) (hdom : p.dom = Set.univ)
    (hran : p.range = Set.univ) :
    ∃ F : M ≃[L] N, ∀ a : p.dom, F a.val = p.toFun a := by
  let f : M → N := fun x => p.toFun ⟨x, hdom.symm ▸ Set.mem_univ x⟩
  let e : M ↪ₑ[L] N :=
    { toFun := f
      map_formula' := by
        intro n φ a
        exact p.elementary φ (fun i => ⟨a i, hdom.symm ▸ Set.mem_univ (a i)⟩) }
  have hsurj : Function.Surjective f := by
    intro b
    have hb : b ∈ p.range := hran.symm ▸ Set.mem_univ b
    obtain ⟨a, ha⟩ := hb
    exact ⟨a.val, ha⟩
  let F : M ≃[L] N :=
    { toEquiv := Equiv.ofBijective f ⟨e.injective, hsurj⟩
      map_fun' := fun f a => e.map_fun f a
      map_rel' := fun r a => e.map_rel r a }
  exact ⟨F, fun _ => rfl⟩

end Map
end
end Lemmatheca.ModelTheory.PartialElementaryMaps
