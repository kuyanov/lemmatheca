import Lemmatheca.StronglyMinimalSets.Minimality
import Lemmatheca.StronglyMinimalSets.Pregeometry

namespace Lemmatheca.ModelTheory.StronglyMinimalSets
open FirstOrder FirstOrder.Language
open Lemmatheca.ModelTheory.Closures
universe u v w z
noncomputable section
variable {L : Language.{u,v}} {M : Type w} [L.Structure M]

private theorem fiber_definable (A : Set M) {α : Type z}
    (φ : L.Formula (α ⊕ Fin 1)) (b : α → M) (hb : ∀ i, b i ∈ A) :
    A.Definable₁ L (fiber φ b) := by
  apply Set.definable_iff_exists_formula_sum.mpr
  let ψ : L.Formula (A ⊕ Fin 1) := φ.relabel (Sum.map (fun i => (⟨b i,hb i⟩ : A)) id)
  refine ⟨ψ,?_⟩
  ext x
  simp only [ψ,Formula.realize_relabel]
  change φ.Realize (Sum.elim b (fun _ : Fin 1 => x 0)) ↔ φ.Realize _
  apply Iff.of_eq
  congr 1
  funext i
  cases i with
  | inl i => rfl
  | inr i =>
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    rfl

private theorem finite_context_bound (T : L.Theory) (hT : StronglyMinimalTheory T)
    [Nonempty M] [M ⊨ T] {α : Type z} [Fintype α]
    (φ : L.Formula (α ⊕ Fin 1)) :
    ∃ N, ∀ b : α → M, Small (fiber φ b) N ∨ Small (fiber φ b)ᶜ N := by
  let e := Fintype.equivFin α
  let ψ := φ.relabel (Sum.map e id)
  obtain ⟨N,hN⟩ := uniform_finite_side T hT ψ
  refine ⟨N,?_⟩
  intro b
  have he : fiber ψ (b ∘ e.symm) = fiber φ b := by
    ext x
    simp only [fiber,Set.mem_ofPred_eq,ψ,Formula.realize_relabel]
    apply Iff.of_eq
    congr 1
    funext i
    cases i <;> simp [Function.comp_apply]
  simpa only [he] using finiteSideBound_model T ψ N hN (b ∘ e.symm)


/-- Parameters first, the distinguished second coordinate next, object last. -/
def verticalParameters {k : ℕ} (c : Fin k → M) (y : M) : (Fin k ⊕ Fin 1) → M :=
  Sum.elim c (fun _ => y)

def guarded {α : Type*} (φ : L.Formula (α ⊕ Fin 1)) (N : ℕ) :
    L.Formula (α ⊕ Fin 1) :=
  φ ⊓ (fiberBound φ N).relabel Sum.inl

theorem guarded_realize {α : Type*} (φ : L.Formula (α ⊕ Fin 1))
    (N : ℕ) (b : α → M) (x : M) :
    x ∈ fiber (guarded φ N) b ↔ x ∈ fiber φ b ∧ (fiberBound φ N).Realize b := by
  simp only [fiber,Set.mem_ofPred_eq,guarded,Formula.realize_inf,Formula.realize_relabel,
    Sum.elim_comp_inl]

theorem guarded_finite_bound [Nonempty M] {α : Type*}
    (φ : L.Formula (α ⊕ Fin 1)) (N : ℕ) (b : α → M) :
    Small (fiber (guarded φ N) b) N := by
  classical
  by_cases hb : (fiberBound φ N).Realize b
  · obtain ⟨s,hs,hφ⟩ := (fiberBound_iff_finite_card φ N b).mp hb
    have he : fiber (guarded φ N) b = (s : Set M) := by
      ext x
      rw [guarded_realize]
      exact ⟨fun h => (hφ x).mp h.1,fun h => ⟨(hφ x).mpr h,hb⟩⟩
    rw [he]
    exact ⟨s.finite_toSet,by simpa using hs⟩
  · have he : fiber (guarded φ N) b = ∅ := by
      ext x
      simp only [guarded_realize,hb,and_false,Set.mem_empty_iff_false]
    rw [he]
    exact ⟨Set.finite_empty,by simp⟩

theorem algebraic_formula_witness (A : Set M) (a b : M)
    (hb : b ∈ acl L (A ∪ {a})) :
    ∃ (k : ℕ) (c : Fin k → M) (φ : L.Formula ((Fin k ⊕ Fin 1) ⊕ Fin 1)),
      (∀ i, c i ∈ A) ∧ b ∈ fiber φ (verticalParameters c a) ∧
      (fiber φ (verticalParameters c a)).Finite := by
  classical
  obtain ⟨s,hs,hfin,hbs⟩ := hb
  obtain ⟨B,hB,hsB⟩ := Set.definable_iff_finitely_definable.mp hs
  obtain ⟨θ,hθ⟩ := Set.definable_iff_exists_formula_sum.mp hsB
  let C := B.erase a
  let e := Fintype.equivFin (C : Set M)
  let c : Fin (Fintype.card (C : Set M)) → M := fun i => (e.symm i).val
  have hc : ∀ i, c i ∈ A := by
    intro i
    have hC := (e.symm i).property
    have hm : c i ∈ B := Finset.mem_of_mem_erase hC
    rcases hB hm with ha | ha
    · exact ha
    · exact False.elim ((Finset.mem_erase.mp hC).1 (Set.mem_singleton_iff.mp ha))
  let names (j : (B : Set M)) : Fin (Fintype.card (C : Set M)) ⊕ Fin 1 :=
    if hj : j.val = a then .inr 0
    else .inl (e ⟨j.val,Finset.mem_erase.mpr ⟨hj,j.property⟩⟩)
  let φ := θ.relabel (Sum.map names id)
  have he : fiber φ (verticalParameters c a) = s := by
    ext x
    simp only [fiber,Set.mem_ofPred_eq,φ,Formula.realize_relabel]
    have hv : Sum.elim (verticalParameters c a) (fun _ : Fin 1 => x) ∘ Sum.map names id =
        Sum.elim (fun j : (B : Set M) => j.val) (fun _ : Fin 1 => x) := by
      funext i
      cases i with
      | inl j =>
        by_cases hj : j.val = a
        · simp only [names,dite_eq_left hj,Function.comp_apply,Sum.map_inl,
            Sum.elim_inl,verticalParameters,Sum.elim_inr]
          exact hj.symm
        · simp only [names,dite_eq_right hj,Function.comp_apply,Sum.map_inl,
            Sum.elim_inl,verticalParameters,Sum.elim_inl,c]
          exact congrArg Subtype.val (e.symm_apply_apply _)
      | inr j => rfl
    rw [hv]
    change (fun _ : Fin 1 => x) ∈ {v | θ.Realize (Sum.elim (↑) v)} ↔ x ∈ s
    rw [←hθ]
    rfl
  exact ⟨_,c,φ,hc,he.symm ▸ hbs,he.symm ▸ hfin⟩

theorem bounded_vertical_relation (T : L.Theory) (hT : StronglyMinimalTheory T)
    [Nonempty M] [M ⊨ T] (A : Set M) (a b : M)
    (hb : b ∈ acl L (A ∪ {a})) :
    ∃ (k : ℕ) (c : Fin k → M) (φ : L.Formula ((Fin k ⊕ Fin 1) ⊕ Fin 1)) (N : ℕ),
      (∀ i, c i ∈ A) ∧ (fiber φ (verticalParameters c a)).Finite ∧
      b ∈ fiber (guarded φ N) (verticalParameters c a) ∧
      ∀ y : M, Small (fiber (guarded φ N) (verticalParameters c y)) N := by
  let : Infinite M := (theory_model_minimal T hT (M := M)).1
  obtain ⟨k,c,φ,hc,hba,hf⟩ := algebraic_formula_witness A a b hb
  obtain ⟨N,hN⟩ := finite_context_bound (M := M) T hT φ
  have hs : Small (fiber φ (verticalParameters c a)) N := by
    rcases hN (verticalParameters c a) with hs | hs
    · exact hs
    · exact False.elim (Set.infinite_univ (by simpa only [Set.union_compl_self] using hf.union hs.1))
  refine ⟨k,c,φ,N,hc,hf,?_,fun y => guarded_finite_bound φ N (verticalParameters c y)⟩
  exact (guarded_realize φ N _ b).mpr ⟨hba,(fiberBound_iff_small φ N _).mpr hs⟩

def transposeIndex {k : ℕ} : ((Fin k ⊕ Fin 1) ⊕ Fin 1) → ((Fin k ⊕ Fin 1) ⊕ Fin 1)
  | .inl (.inl i) => .inl (.inl i)
  | .inl (.inr i) => .inr i
  | .inr i => .inl (.inr i)

def horizontal {k : ℕ} (φ : L.Formula ((Fin k ⊕ Fin 1) ⊕ Fin 1)) :
    L.Formula ((Fin k ⊕ Fin 1) ⊕ Fin 1) := φ.relabel transposeIndex

theorem horizontal_realize {k : ℕ}
    (φ : L.Formula ((Fin k ⊕ Fin 1) ⊕ Fin 1)) (c : Fin k → M) (x y : M) :
    y ∈ fiber (horizontal φ) (verticalParameters c x) ↔
      x ∈ fiber φ (verticalParameters c y) := by
  simp only [fiber,Set.mem_ofPred_eq,horizontal,Formula.realize_relabel]
  apply Iff.of_eq
  congr 1
  funext i
  rcases i with (i | i) | i
  · rfl
  · rfl
  · rfl

def cofiniteHorizontals {k : ℕ}
    (φ : L.Formula ((Fin k ⊕ Fin 1) ⊕ Fin 1)) (c : Fin k → M) : Set M :=
  {x | Cofinite (fiber (horizontal φ) (verticalParameters c x))}

def horizontalCofiniteFormula {k : ℕ}
    (φ : L.Formula ((Fin k ⊕ Fin 1) ⊕ Fin 1)) (K : ℕ) : L.Formula (Fin k ⊕ Fin 1) :=
  cofiniteFormula (horizontal φ) K

theorem cofiniteHorizontals_definable (T : L.Theory) (hT : StronglyMinimalTheory T)
    [Nonempty M] [M ⊨ T] (A : Set M) {k : ℕ} (c : Fin k → M) (hc : ∀ i, c i ∈ A)
    (φ : L.Formula ((Fin k ⊕ Fin 1) ⊕ Fin 1)) :
    ∃ K : ℕ, (∀ x, (horizontalCofiniteFormula φ K).Realize (verticalParameters c x) ↔
      x ∈ cofiniteHorizontals φ c) ∧ A.Definable₁ L (cofiniteHorizontals φ c) := by
  let : Infinite M := (theory_model_minimal T hT (M := M)).1
  obtain ⟨K,hK⟩ := finite_context_bound (M := M) T hT (horizontal φ)
  have he : ∀ x, (horizontalCofiniteFormula φ K).Realize (verticalParameters c x) ↔
      x ∈ cofiniteHorizontals φ c := by
    intro x
    rw [horizontalCofiniteFormula,cofiniteFormula,Formula.realize_not,fiberBound_iff_small]
    change ¬Small (fiber (horizontal φ) (verticalParameters c x)) K ↔
      Cofinite (fiber (horizontal φ) (verticalParameters c x))
    constructor
    · intro hn
      rcases hK (verticalParameters c x) with hf | hf
      · exact (hn hf).elim
      · exact hf.1
    · intro hf hs
      exact Set.infinite_univ (by simpa only [Set.union_compl_self] using hs.1.union hf)
  refine ⟨K,he,?_⟩
  have hd := fiber_definable A (horizontalCofiniteFormula φ K) c hc
  have hset : fiber (horizontalCofiniteFormula φ K) c = cofiniteHorizontals φ c := Set.ext he
  exact hset ▸ hd

theorem cofiniteHorizontals_small [Infinite M] {k : ℕ}
    (φ : L.Formula ((Fin k ⊕ Fin 1) ⊕ Fin 1)) (c : Fin k → M) (N : ℕ)
    (hv : ∀ y : M, Small (fiber φ (verticalParameters c y)) N) :
    Small (cofiniteHorizontals φ c) N := by
  classical
  by_contra hn
  have hn' : ¬Small (cofiniteHorizontals φ c) ((N+1)-1) := by simpa using hn
  obtain ⟨a,ha⟩ := (not_small_iff_embedding _ (N+1) (Nat.succ_pos _)).mp hn'
  have hfinite (i : Fin (N+1)) :
      (fiber (horizontal φ) (verticalParameters c (a i)))ᶜ.Finite := ha i
  have hUnion : (⋃ i : Fin (N+1), (fiber (horizontal φ) (verticalParameters c (a i)))ᶜ).Finite :=
    Set.finite_iUnion hfinite
  obtain ⟨y,hy⟩ := hUnion.exists_notMem
  have hya (i : Fin (N+1)) : a i ∈ fiber φ (verticalParameters c y) := by
    apply (horizontal_realize φ c (a i) y).mp
    by_contra h
    exact hy (Set.mem_iUnion.mpr ⟨i,h⟩)
  have hbad := (not_small_iff_embedding (fiber φ (verticalParameters c y))
    (N+1) (Nat.succ_pos _)).mpr ⟨a,hya⟩
  exact hbad (by simpa using hv y)

theorem horizontal_cofinite_of_not_algebraic (T : L.Theory) (hT : StronglyMinimalTheory T)
    [Nonempty M] [M ⊨ T] (A : Set M) {k : ℕ} (c : Fin k → M) (hc : ∀ i, c i ∈ A)
    (φ : L.Formula ((Fin k ⊕ Fin 1) ⊕ Fin 1)) (a b : M)
    (hab : b ∈ fiber φ (verticalParameters c a))
    (ha : a ∉ acl L (A ∪ {b})) : b ∈ cofiniteHorizontals φ c := by
  have hm := theory_model_minimal T hT (M := M)
  have hd : (A ∪ {b}).Definable₁ L (fiber (horizontal φ) (verticalParameters c b)) :=
    fiber_definable _ _ _ (by
      intro i
      cases i with
      | inl i => exact Or.inl (hc i)
      | inr i => exact Or.inr rfl)
  rcases hm.2 _ (hd.mono (Set.subset_univ _)) with hf | hf
  · exact False.elim (ha ⟨_,hd,hf,(horizontal_realize φ c b a).mpr hab⟩)
  · exact hf

theorem algebraic_exchange (T : L.Theory) (hT : StronglyMinimalTheory T)
    [Nonempty M] [M ⊨ T] (A : Set M) (a b : M)
    (hb : b ∈ acl L (A ∪ {a}) \ acl L A) : a ∈ acl L (A ∪ {b}) := by
  classical
  by_contra ha
  let : Infinite M := (theory_model_minimal T hT (M := M)).1
  obtain ⟨k,c,φ,N,hc,_,hbφ,hv⟩ := bounded_vertical_relation T hT A a b hb.1
  have hbC := horizontal_cofinite_of_not_algebraic T hT A c hc (guarded φ N) a b hbφ ha
  obtain ⟨_,_,hC⟩ := cofiniteHorizontals_definable T hT A c hc (guarded φ N)
  have hsmall := cofiniteHorizontals_small (guarded φ N) c N hv
  exact hb.2 ⟨cofiniteHorizontals (guarded φ N) c,hC,hsmall.1,hbC⟩

def aclPregeometry (T : L.Theory) (hT : StronglyMinimalTheory T)
    [Nonempty M] [M ⊨ T] : Pregeometry M where
  cl := acl L
  extensive A := (subset_dcl A).trans (dcl_subset_acl A)
  monotone h := acl_mono h
  idempotent A := acl_idempotent A
  finite_character _ _ := mem_acl_finite
  exchange A a b := algebraic_exchange T hT A a b

end
end Lemmatheca.ModelTheory.StronglyMinimalSets
