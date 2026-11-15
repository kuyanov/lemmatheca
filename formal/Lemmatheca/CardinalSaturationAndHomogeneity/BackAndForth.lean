import Lemmatheca.CardinalSaturationAndHomogeneity.Steps

namespace Lemmatheca.ModelTheory.CardinalSaturation

open FirstOrder FirstOrder.Language
open PartialElementaryMaps Cardinal

universe u v w w' z

variable {L : Language.{u, v}} {M : Type w} {N : Type w'}
variable [L.Structure M] [L.Structure N] [Nonempty M] [Nonempty N]
variable {κ : Cardinal.{z}}

theorem elementary_embedding (hκ : ℵ₀ ≤ κ) (hN : IsSaturated κ L N)
    (hMsize : AtMost κ M) (p : Map L M N) (hp : Below κ p.dom) :
    ∃ e : M ↪ₑ[L] N, ∀ a : p.dom, e a.val = p.toFun a := by
  classical
  obtain ⟨m, hm⟩ := ordinal_enumeration hMsize
  let step : Ordinal.{z} → Map L M N → Map L M N := fun α q => stepAt hκ hN q (m α)
  let F := mapSequence p step
  have hs : ∀ α q, q ≤ step α q := fun α q => stepAt_extends hκ hN q (m α)
  have hcont := (mapSequence_continuous p step hs).1
  have hadd : AddsAtMostTwo (fun α => (F α).dom) := by
    intro α
    change #((mapSequence p step (α + 1)).dom \ (F α).dom : Set M) ≤ 2
    rw [mapSequence_succ]
    apply two_point_difference (F α).dom (step α (F α)).dom (m α) (m α)
    simpa only [Set.insert_idem] using (stepAt_sets hκ hN (F α) (m α)).1
  have hzero : Below κ (F 0).dom := by simpa only [F, mapSequence_zero] using hp
  have hsmall (α : Ordinal.{z}) (hα : α < κ.ord) : Below κ (F α).dom :=
    stage_below hκ (fun α => (F α).dom) hcont hadd hzero α hα
  have hmono : Monotone F := mapSequence_monotone p step hs
  have hdom : (F κ.ord).dom = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨α, hα, hx⟩ := hm x
    have hi : x ∈ (F (α + 1)).dom := by
      change x ∈ (mapSequence p step (α + 1)).dom
      rw [mapSequence_succ]
      change x ∈ (stepAt hκ hN (F α) (m α)).dom
      rw [stepAt_dom hκ hN (F α) (hsmall α hα) (m α)]
      exact Or.inl hx.symm
    exact Map.dom_mono (hmono (Order.succ_le_iff.mpr hα)) hi
  let q := F κ.ord
  let e : M ↪ₑ[L] N := {
    toFun := fun x => q.toFun ⟨x, hdom.symm ▸ Set.mem_univ x⟩
    map_formula' := fun {n} φ a => q.elementary φ
      (fun i => ⟨a i, hdom.symm ▸ Set.mem_univ (a i)⟩) }
  have hpq : p ≤ q := by
    have h := hmono (show (0 : Ordinal.{z}) ≤ κ.ord from bot_le)
    simpa only [F, mapSequence_zero] using h
  exact ⟨e, fun a => Map.apply_mono hpq a⟩

theorem isomorphism_extension (hκ : ℵ₀ ≤ κ)
    (hM : IsSaturated κ L M) (hN : IsSaturated κ L N)
    (hMsize : AtMost κ M) (hNsize : AtMost κ N)
    (p : Map L M N) (hp : Below κ p.dom) :
    ∃ e : M ≃[L] N, ∀ a : p.dom, e a.val = p.toFun a := by
  classical
  obtain ⟨m, hm⟩ := ordinal_enumeration hMsize
  obtain ⟨n, hn⟩ := ordinal_enumeration hNsize
  let step : Ordinal.{z} → Map L M N → Map L M N :=
    fun α q => roundAt hκ hM hN q (m α) (n α)
  let F := mapSequence p step
  have hs : ∀ α q, q ≤ step α q := fun α q => roundAt_extends hκ hM hN q (m α) (n α)
  have hcont := (mapSequence_continuous p step hs).1
  have hadd : AddsAtMostTwo (fun α => (F α).dom) := by
    intro α
    change #((mapSequence p step (α + 1)).dom \ (F α).dom : Set M) ≤ 2
    rw [mapSequence_succ]
    obtain ⟨c, hc⟩ := (roundAt_sets hκ hM hN (F α) (m α) (n α)).1
    exact two_point_difference _ _ c (m α) hc
  have hzero : Below κ (F 0).dom := by simpa only [F, mapSequence_zero] using hp
  have hsmall (α : Ordinal.{z}) (hα : α < κ.ord) : Below κ (F α).dom :=
    stage_below hκ (fun α => (F α).dom) hcont hadd hzero α hα
  have hmono : Monotone F := mapSequence_monotone p step hs
  have hrequests (α : Ordinal.{z}) (hα : α < κ.ord) :
      m α ∈ (F (α + 1)).dom ∧ n α ∈ (F (α + 1)).range := by
    change m α ∈ (mapSequence p step (α + 1)).dom ∧
      n α ∈ (mapSequence p step (α + 1)).range
    rw [mapSequence_succ]
    exact roundAt_requests hκ hM hN (F α) (hsmall α hα) (m α) (n α)
  have hdom : (F κ.ord).dom = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨α, hα, hx⟩ := hm x
    rw [← hx]
    exact Map.dom_mono (hmono (Order.succ_le_iff.mpr hα)) (hrequests α hα).1
  have hran : (F κ.ord).range = Set.univ := by
    apply Set.eq_univ_of_forall
    intro y
    obtain ⟨α, hα, hy⟩ := hn y
    rw [← hy]
    exact Map.range_mono (hmono (Order.succ_le_iff.mpr hα)) (hrequests α hα).2
  have hpq : p ≤ F κ.ord := by
    have h := hmono (show (0 : Ordinal.{z}) ≤ κ.ord from bot_le)
    simpa only [F, mapSequence_zero] using h
  obtain ⟨e, he⟩ := Map.total_isomorphism (F κ.ord) hdom hran
  refine ⟨e, fun a => ?_⟩
  exact (he ⟨a.val, Map.dom_mono hpq a.property⟩).trans (Map.apply_mono hpq a)

/-- Equality of actual named complete types gives the specified small tuple map. -/
theorem tuple_map (hκ : ℵ₀ ≤ κ) {n : ℕ} (A : Set M) (hA : Below κ A)
    (a b : Fin n → M)
    (hab : (L[[A]].completeTheory M).typeOf a =
      (L[[A]].completeTheory M).typeOf b) :
    ∃ p : Map L M M,
      p.dom = A ∪ Set.range a ∧ Below κ p.dom ∧
      (∀ x : A, ∃ hx : x.val ∈ p.dom, p.toFun ⟨x.val, hx⟩ = x.val) ∧
      (∀ i, ∃ hi : a i ∈ p.dom, p.toFun ⟨a i, hi⟩ = b i) := by
  classical
  let source : A ⊕ Fin n → M := Sum.elim Subtype.val a
  let target : A ⊕ Fin n → M := Sum.elim Subtype.val b
  have htruth (φ : L.Formula (A ⊕ Fin n)) : φ.Realize source ↔ φ.Realize target := by
    let ψ : L[[A]].Formula (Fin n) := BoundedFormula.constantsVarsEquiv.symm φ
    have hset := congrArg Types.formulas hab
    rw [Types.formulas_typeOf, Types.formulas_typeOf] at hset
    have hh : ψ.Realize a ↔ ψ.Realize b := Set.ext_iff.mp hset ψ
    have ha := BoundedFormula.realize_constantsVarsEquiv (M := M) (φ := ψ)
      (v := a) (xs := default)
    have hb := BoundedFormula.realize_constantsVarsEquiv (M := M) (φ := ψ)
      (v := b) (xs := default)
    have heq : BoundedFormula.constantsVarsEquiv ψ = φ := Equiv.apply_symm_apply _ _
    rw [heq] at ha hb
    exact ha.trans (hh.trans hb.symm)
  have hequal (i j : A ⊕ Fin n) : source i = source j ↔ target i = target j := by
    simpa only [Formula.realize_equal, Term.realize_var] using
      htruth ((Term.var i).equal (Term.var j))
  let D := Set.range source
  let repr (x : D) : A ⊕ Fin n := x.property.choose
  have hrepr (x : D) : source (repr x) = x.val := x.property.choose_spec
  let f : D → M := target ∘ repr
  have hf (i : A ⊕ Fin n) (hi : source i ∈ D) : f ⟨source i, hi⟩ = target i :=
    (hequal (repr ⟨source i, hi⟩) i).mp (hrepr ⟨source i, hi⟩)
  let p : Map L M M := {
    dom := D
    toFun := f
    injective := by
      intro x y hxy
      apply Subtype.ext
      exact (hrepr x).symm.trans (((hequal (repr x) (repr y)).mpr hxy).trans (hrepr y))
    elementary := by
      intro k φ c
      have h := htruth (φ.relabel (repr ∘ c))
      rw [Formula.realize_relabel, Formula.realize_relabel] at h
      have hs : source ∘ (repr ∘ c) = Subtype.val ∘ c := by
        funext i
        exact hrepr (c i)
      have ht : target ∘ (repr ∘ c) = f ∘ c := rfl
      rw [hs, ht] at h
      exact h.symm }
  have hd : D = A ∪ Set.range a := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      cases i with
      | inl d => exact Or.inl d.property
      | inr i => exact Or.inr ⟨i, rfl⟩
    · rintro (hx | ⟨i, rfl⟩)
      · exact ⟨Sum.inl ⟨x, hx⟩, rfl⟩
      · exact ⟨Sum.inr i, rfl⟩
  have hD : Below κ D := hd.symm ▸ below_union_finite hκ A (Set.range a) hA (Set.finite_range a)
  refine ⟨p, hd, hD, ?_, ?_⟩
  · intro x
    exact ⟨⟨Sum.inl x, rfl⟩, hf (Sum.inl x) _⟩
  · intro i
    exact ⟨⟨Sum.inr i, rfl⟩, hf (Sum.inr i) _⟩

theorem tuple_homogeneity (hκ : ℵ₀ ≤ κ) (hM : IsSaturated κ L M)
    (hMsize : AtMost κ M) {n : ℕ} (A : Set M) (hA : Below κ A)
    (a b : Fin n → M)
    (hab : (L[[A]].completeTheory M).typeOf a =
      (L[[A]].completeTheory M).typeOf b) :
    ∃ e : M ≃[L] M, (∀ x : A, e x.val = x.val) ∧ ∀ i, e (a i) = b i := by
  obtain ⟨p, _, hp, hfix, hmove⟩ := tuple_map hκ A hA a b hab
  obtain ⟨e, he⟩ := isomorphism_extension hκ hM hM hMsize hMsize p hp
  refine ⟨e, ?_, ?_⟩
  · intro x
    obtain ⟨hx, hfx⟩ := hfix x
    exact (he ⟨x.val, hx⟩).trans hfx
  · intro i
    obtain ⟨hi, hfi⟩ := hmove i
    exact (he ⟨a i, hi⟩).trans hfi

end Lemmatheca.ModelTheory.CardinalSaturation
