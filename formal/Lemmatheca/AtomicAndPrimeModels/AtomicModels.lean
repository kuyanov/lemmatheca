import Lemmatheca.AtomicAndPrimeModels.AtomicTypes
import Lemmatheca.AtomicAndPrimeModels.PartialElementaryMaps
import Lemmatheca.ElementarySubmodels.ElementarySubmodels

/-! Elementary embeddings and prescribed isomorphisms of countable atomic models. -/

namespace Lemmatheca.ModelTheory.AtomicAndPrimeModels

open FirstOrder FirstOrder.Language
open Lemmatheca.ModelTheory.Types Lemmatheca.ModelTheory.IsolatedTypes
open Lemmatheca.ModelTheory.PartialElementaryMaps
open scoped FirstOrder

variable {L : Language.{0, 0}} {T : L.Theory}
variable {M N : Type} [L.Structure M] [L.Structure N]
variable [Nonempty M] [Nonempty N] [M ⊨ T] [N ⊨ T]

theorem typeOf_eq_iff {n : ℕ} (a : Fin n → M) (b : Fin n → N) :
    T.typeOf a = T.typeOf b ↔
      ∀ φ : L.Formula (Fin n), φ.Realize a ↔ φ.Realize b := by
  constructor
  · intro hab φ
    have h : φ ∈ formulas (T.typeOf a) ↔ φ ∈ formulas (T.typeOf b) := by rw [hab]
    exact Theory.CompleteType.formula_mem_typeOf.symm.trans
      (h.trans Theory.CompleteType.formula_mem_typeOf)
  · intro h
    apply SetLike.ext
    intro γ
    simpa only [Theory.CompleteType.mem_typeOf] using h (Formula.equivSentence.symm γ)

theorem tuple_map_iff {n : ℕ} (a : Fin n → M) (b : Fin n → N) :
    T.typeOf a = T.typeOf b ↔
      ∃ p : FiniteMap L M N, p.dom = Set.range a ∧ p.range = Set.range b ∧
        ∀ i, ∃ ha : a i ∈ p.dom, p.toFun ⟨a i, ha⟩ = b i := by
  exact (typeOf_eq_iff a b).trans (FiniteMap.tuple_map_iff a b)

private theorem append_relabel_realize {X : Type} [L.Structure X] {m n : ℕ}
    (θ : L.Formula (Fin (m + n))) (a : Fin m → X) (b : Fin n → X) :
    (θ.relabel finSumFinEquiv.symm).Realize (Sum.elim a b) ↔
      θ.Realize (Fin.append a b) := by
  rw [Formula.realize_relabel]
  have h : Sum.elim a b ∘ finSumFinEquiv.symm = Fin.append a b := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp
  rw [h]

theorem one_point_extension (hM : IsAtomic T M) (p : FiniteMap L M N) (a : M) :
    ∃ q : FiniteMap L M N, p ≤ q ∧ q.dom = insert a p.dom := by
  classical
  let := Fintype.ofFinite p.dom
  let n := Fintype.card p.dom
  let e : p.dom ≃ Fin n := Fintype.equivFin p.dom
  let c : Fin n → M := Subtype.val ∘ e.symm
  let d : Fin n → N := p.toFun ∘ e.symm
  let a₁ : Fin 1 → M := fun _ => a
  obtain ⟨θ, hθ⟩ := hM (n + 1) (Fin.append c a₁)
  let θ' : L.Formula (Fin n ⊕ Fin 1) := θ.relabel finSumFinEquiv.symm
  let ψ := θ'.iExs (Fin 1)
  have hψc : ψ.Realize c := Formula.realize_iExs.mpr
    ⟨a₁, (append_relabel_realize θ c a₁).mpr
      (Theory.CompleteType.formula_mem_typeOf.mp hθ.1)⟩
  have hψd : ψ.Realize d := (p.elementary ψ e.symm).mpr hψc
  obtain ⟨b₁, hb₁⟩ := Formula.realize_iExs.mp hψd
  have hθN : θ.Realize (Fin.append d b₁) := (append_relabel_realize θ d b₁).mp hb₁
  have ht : T.typeOf (Fin.append c a₁) = T.typeOf (Fin.append d b₁) :=
    (realizes_complete_iff _ _).mp ((isolator_realizes _ θ hθ _).mp hθN)
  let q := FiniteMap.ofTuple (Fin.append c a₁) (Fin.append d b₁)
    ((typeOf_eq_iff _ _).mp ht)
  have hc : Set.range c = p.dom := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact (e.symm i).property
    · intro hx
      exact ⟨e ⟨x, hx⟩, congrArg Subtype.val (e.symm_apply_apply ⟨x, hx⟩)⟩
  have hdom : q.dom = insert a p.dom := by
    change Set.range (Fin.append c a₁) = _
    rw [Fin.append_right_eq_snoc, Fin.range_snoc, hc]
  refine ⟨q, ⟨?_, ?_⟩, hdom⟩
  · intro x hx
    exact hdom.symm ▸ Set.mem_insert_of_mem a hx
  · intro x
    have hq := FiniteMap.ofTuple_apply (Fin.append c a₁) (Fin.append d b₁)
      ((typeOf_eq_iff _ _).mp ht) (Fin.castAdd 1 (e x))
    simpa only [Fin.append_left, c, d, Function.comp_apply, e.symm_apply_apply] using hq

theorem countable_atomic_embedding [Countable M]
    (hM : IsAtomic T M) (p : FiniteMap L M N) :
    ∃ f : M ↪ₑ[L] N, ∀ a : p.dom, f a = p.toFun a := by
  apply FiniteMap.countable_embedding ?_ p
  intro p a
  obtain ⟨q, hpq, hdom⟩ := one_point_extension hM p a
  exact ⟨q, hpq, hdom.symm ▸ Set.mem_insert a p.dom⟩

theorem countable_atomic_prime [Countable M] (hT : T.IsComplete)
    (hM : IsAtomic T M) : IsPrime T M := by
  intro N
  obtain ⟨f, _⟩ := countable_atomic_embedding hM
    (FiniteMap.empty (hT.models_elementarily_equivalent M N))
  exact ⟨f⟩

theorem countable_atomic_isomorphism [Countable M] [Countable N]
    (_hT : T.IsComplete) (hM : IsAtomic T M) (hN : IsAtomic T N)
    (p : FiniteMap L M N) :
    ∃ f : M ≃[L] N, ∀ a : p.dom, f a = p.toFun a := by
  classical
  let S : BackAndForth.BackForthSystem L M N := {
    maps := Set.range (fun q : FiniteMap L M N => q.toFinitePartialIso)
    nonempty := ⟨p.toFinitePartialIso, p, rfl⟩
    forth := by
      rintro _ ⟨q, rfl⟩ a
      obtain ⟨r, hqr, hdom⟩ := one_point_extension hM q a
      exact ⟨r.toFinitePartialIso, ⟨r, rfl⟩, hqr,
        hdom.symm ▸ Set.mem_insert a q.dom⟩
    back := by
      rintro _ ⟨q, rfl⟩ b
      obtain ⟨r, hqr, hdom⟩ := one_point_extension hN q.symm b
      have hle : q ≤ r.symm := by
        simpa only [FiniteMap.symm_symm] using FiniteMap.symm_le_symm hqr
      let b' : r.dom := ⟨b, hdom.symm ▸ Set.mem_insert b q.symm.dom⟩
      exact ⟨r.symm.toFinitePartialIso, ⟨r.symm, rfl⟩, hle,
        r.rangeEquiv b', r.symm_apply b'⟩ }
  exact BackAndForth.countable_isomorphism S p.toFinitePartialIso ⟨p, rfl⟩

theorem countable_atomic_tuple_isomorphism [Countable M] [Countable N]
    (hT : T.IsComplete) (hM : IsAtomic T M) (hN : IsAtomic T N)
    {n : ℕ} (a : Fin n → M) (b : Fin n → N) (hab : T.typeOf a = T.typeOf b) :
    ∃ f : M ≃[L] N, ∀ i, f (a i) = b i := by
  obtain ⟨p, _, _, hp⟩ := (tuple_map_iff a b).mp hab
  obtain ⟨f, hf⟩ := countable_atomic_isomorphism hT hM hN p
  refine ⟨f, fun i => ?_⟩
  obtain ⟨hi, hpi⟩ := hp i
  exact (hf ⟨a i, hi⟩).trans hpi

theorem countable_atomic_unique [Countable M] [Countable N]
    (hT : T.IsComplete) (hM : IsAtomic T M) (hN : IsAtomic T N) :
    Nonempty (M ≃[L] N) := by
  obtain ⟨f, _⟩ := countable_atomic_isomorphism hT hM hN
    (FiniteMap.empty (hT.models_elementarily_equivalent M N))
  exact ⟨f⟩

theorem prime_countable [Countable L.Symbols] (_hT : T.IsComplete)
    (hM : IsPrime T M) : Countable M := by
  classical
  let a : M := Classical.choice (inferInstance : Nonempty M)
  obtain ⟨S, hS, hc⟩ := ElementarySubmodels.exists_countable_elementarySubstructure
    (L := L) ({a} : Set M) (Set.countable_singleton a)
  let : Nonempty S := ⟨⟨a, hS (Set.mem_singleton a)⟩⟩
  let : S ⊨ T := (S.subtype.theory_model_iff T).mpr (inferInstance : M ⊨ T)
  obtain ⟨f⟩ := hM (Theory.ModelType.of T S)
  let : Countable (Theory.ModelType.of T S) := hc
  exact Function.Injective.countable f.injective

theorem prime_atomic [Countable L.Symbols] (hT : T.IsComplete)
    (hM : IsPrime T M) : IsAtomic T M := by
  intro n a
  by_contra hn
  obtain ⟨N, SN, hne, _, hmodel, homit⟩ := OmittingTypes.exists_countable_omitting
    hT hT.1 (I := Unit) (n := fun _ => n) (fun _ => T.typeOf a) (fun _ => hn)
  let := SN
  let := hne
  let := hmodel
  obtain ⟨f⟩ := hM (Theory.ModelType.of T N)
  apply homit ()
  refine ⟨f ∘ a, fun φ hφ => ?_⟩
  exact (f.map_formula φ a).mpr (Theory.CompleteType.formula_mem_typeOf.mp hφ)

theorem prime_iff_countable_atomic [Countable L.Symbols] (hT : T.IsComplete) :
    IsPrime T M ↔ Countable M ∧ IsAtomic T M := by
  constructor
  · intro h
    exact ⟨prime_countable hT h, prime_atomic hT h⟩
  · rintro ⟨hc, ha⟩
    let := hc
    exact countable_atomic_prime hT ha

end Lemmatheca.ModelTheory.AtomicAndPrimeModels
