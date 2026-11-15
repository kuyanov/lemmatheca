import Lemmatheca.StableFormulasAndDefinabilityOfTypes.LocalTypes
import Lemmatheca.PartitionRelations.PartitionRelations

namespace Lemmatheca.ModelTheory.StableDefinability
open FirstOrder FirstOrder.Language
open Lemmatheca.ModelTheory.OrderPatternsAndStability
universe u v w
noncomputable section
variable {L : Language.{u,v}} {M : Type w} [L.Structure M] {n m k : ℕ}

def Separates (φ : L.Formula (Fin (n+m))) (P : Set (Fin m → M))
    (a : Fin k → Fin n → M) : Prop :=
  ∀ b ∈ P, ∀ c ∉ P, ∃ i : Fin k, ¬ (Truth φ (a i) b ↔ Truth φ (a i) c)

def rowVector (φ : L.Formula (Fin (n+m))) (a : Fin k → Fin n → M)
    (b : Fin m → M) : Fin k → Bool := by
  classical
  exact fun i => decide (Truth φ (a i) b)

theorem separates_iff_vectors (φ : L.Formula (Fin (n+m))) (P : Set (Fin m → M))
    (a : Fin k → Fin n → M) :
    Separates φ P a ↔ ∀ b ∈ P, ∀ c ∉ P, rowVector φ a b ≠ rowVector φ a c := by
  classical
  constructor
  · intro h b hb c hc he
    obtain ⟨i,hi⟩ := h b hb c hc
    exact hi (decide_eq_decide.mp (congrFun he i))
  · intro h b hb c hc
    by_contra hn
    apply h b hb c hc
    push Not at hn
    funext i
    exact decide_eq_decide.mpr (hn i)

theorem separates_empty_iff (φ : L.Formula (Fin (n+m))) (P : Set (Fin m → M)) :
    Separates φ P (Fin.elim0 : Fin 0 → Fin n → M) ↔ P = ∅ ∨ P = Set.univ := by
  classical
  constructor
  · intro h
    by_cases hp : P = ∅
    · exact Or.inl hp
    · right
      apply Set.eq_univ_of_forall
      intro c
      by_contra hc
      obtain ⟨b,hb⟩ := Set.nonempty_iff_ne_empty.mpr hp
      obtain ⟨i,_⟩ := h b hb c hc
      exact Fin.elim0 i
  · rintro (rfl | rfl)
    · intro b hb
      exact False.elim hb
    · intro b _ c hc
      exact False.elim (hc (Set.mem_univ _))

/-- These arrays retain their actual rows and both oppositely signed parameter sequences. -/
structure Triangle (φ : L.Formula (Fin (n+m))) (P : Set (Fin m → M))
    (a : ℕ → Fin n → M) (b c : ℕ → Fin m → M) : Prop where
  positive : ∀ i, b i ∈ P
  negative : ∀ i, c i ∉ P
  lower_true : ∀ i j, j ≤ i → Truth φ (a i) (b j)
  lower_false : ∀ i j, j ≤ i → ¬ Truth φ (a i) (c j)
  upper_agree : ∀ i j, i < j → (Truth φ (a i) (b j) ↔ Truth φ (a i) (c j))

private structure SignedTriple (n m : ℕ) (M : Type w) (P : Set (Fin m → M)) where
  a : Fin n → M
  b : Fin m → M
  c : Fin m → M
  positive : b ∈ P
  negative : c ∉ P

theorem exists_triangle (φ : L.Formula (Fin (n+m))) (P : Set (Fin m → M))
    (hP : IsLocalType φ P)
    (hnot : ¬ ∃ k, ∃ a : Fin k → Fin n → M, Separates φ P a) :
    ∃ (a : ℕ → Fin n → M) (b c : ℕ → Fin m → M), Triangle φ P a b c := by
  classical
  have pair (k : ℕ) (a : Fin k → Fin n → M) :
      ∃ b ∈ P, ∃ c ∉ P, ∀ i : Fin k, Truth φ (a i) b ↔ Truth φ (a i) c := by
    have hn : ¬ Separates φ P a := fun hh => hnot ⟨k,a,hh⟩
    unfold Separates at hn
    push Not at hn
    exact hn
  let Triple := SignedTriple n m M P
  have next (l : List Triple) : ∃ t : Triple,
      (∀ u ∈ l, Truth φ t.a u.b ∧ ¬Truth φ t.a u.c) ∧
      Truth φ t.a t.b ∧ ¬Truth φ t.a t.c ∧
      (∀ u ∈ l, Truth φ u.a t.b ↔ Truth φ u.a t.c) := by
    obtain ⟨b,hb,c,hc,hagree⟩ := pair l.length (fun i => (l.get i).a)
    let Q : Finset (Fin m → M) :=
      insert b (insert c (l.toFinset.biUnion (fun u => {u.b,u.c})))
    obtain ⟨a,ha⟩ := hP Q
    have old_b (u : Triple) (hu : u ∈ l) : u.b ∈ Q := by
      apply Finset.mem_insert_of_mem
      apply Finset.mem_insert_of_mem
      exact Finset.mem_biUnion.mpr ⟨u,List.mem_toFinset.mpr hu,by simp⟩
    have old_c (u : Triple) (hu : u ∈ l) : u.c ∈ Q := by
      apply Finset.mem_insert_of_mem
      apply Finset.mem_insert_of_mem
      exact Finset.mem_biUnion.mpr ⟨u,List.mem_toFinset.mpr hu,by simp⟩
    refine ⟨⟨a,b,c,hb,hc⟩,?_,?_,?_,?_⟩
    · intro u hu
      exact ⟨(ha u.b (old_b u hu)).mpr u.positive,
        fun ht => u.negative ((ha u.c (old_c u hu)).mp ht)⟩
    · exact (ha b (Finset.mem_insert_self _ _)).mpr hb
    · exact fun ht => hc ((ha c (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))).mp ht)
    · intro u hu
      obtain ⟨i,hi⟩ := List.mem_iff_get.mp hu
      simpa only [hi] using hagree i
  let history (i : ℕ) : List Triple :=
    Nat.rec [] (fun _ l => l ++ [(next l).choose]) i
  let t (i : ℕ) : Triple := (next (history i)).choose
  have hh (i : ℕ) : history (i+1) = history i ++ [t i] := rfl
  have ht (i : ℕ) := (next (history i)).choose_spec
  have mem (j : ℕ) : ∀ i, i < j → t i ∈ history j := by
    induction j with
    | zero => intro i hi; omega
    | succ j ih =>
      intro i hij
      rw [hh]
      by_cases he : i = j
      · subst i
        exact List.mem_append_right _ (List.mem_singleton_self _)
      · exact List.mem_append_left _ (ih i (by omega))
  refine ⟨fun i => (t i).a,fun i => (t i).b,fun i => (t i).c,
    ⟨fun i => (t i).positive,fun i => (t i).negative,?_,?_,?_⟩⟩
  · intro i j hij
    by_cases he : j = i
    · subst j
      exact (ht i).2.1
    · exact ((ht i).1 (t j) (mem i j (by omega))).1
  · intro i j hij
    by_cases he : j = i
    · subst j
      exact (ht i).2.2.1
    · exact ((ht i).1 (t j) (mem i j (by omega))).2
  · intro i j hij
    exact (ht j).2.2.2 (t i) (mem j i hij)

theorem homogeneous_upper (φ : L.Formula (Fin (n+m))) (P : Set (Fin m → M))
    (a : ℕ → Fin n → M) (b c : ℕ → Fin m → M) (h : Triangle φ P a b c) :
    ∃ f : ℕ → ℕ, StrictMono f ∧ ∃ ε : Bool,
      ∀ i j, i < j → (Truth φ (a (f i)) (b (f j)) ↔ ε = true) := by
  classical
  let color : Lemmatheca.SetTheory.PartitionRelations.Coloring ℕ 2 (Fin 2) := fun s =>
    if Truth φ (a (s.val.min' (by have hcard := s.property; exact Finset.card_pos.mp (by omega))))
        (c (s.val.max' (by have hcard := s.property; exact Finset.card_pos.mp (by omega))))
      then 1 else 0
  obtain ⟨H,hH,ε,hε⟩ := Lemmatheca.SetTheory.PartitionRelations.infinite_ramsey
    (by decide : 0 < 2) (by decide : 0 < 2) color
  let : Infinite H := hH.to_subtype
  let e : ℕ ≃o H := Nat.Subtype.orderIsoOfNat H
  let f : ℕ → ℕ := fun i => (e i).val
  have hf : StrictMono f := fun _ _ hij => e.strictMono hij
  refine ⟨f,hf,decide (ε = 1),fun i j hij => ?_⟩
  let s : Lemmatheca.SetTheory.PartitionRelations.Subsets ℕ 2 :=
    ⟨{f i,f j},by simp [ne_of_lt (hf hij)]⟩
  have hs : (↑s.val : Set ℕ) ⊆ H := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact (e i).property
    · have he := Finset.mem_singleton.mp hx
      exact he ▸ (e j).property
  have hc := hε s hs
  have hv : (if Truth φ (a (f i)) (c (f j)) then (1 : Fin 2) else 0) = ε := by
    simpa only [color,s,Finset.min'_pair,Finset.max'_pair,
      min_eq_left (hf hij).le,max_eq_right (hf hij).le] using hc
  have he : Truth φ (a (f i)) (c (f j)) ↔ ε = 1 := by
    constructor
    · intro ht
      have hv' : (1 : Fin 2) = ε := by simpa only [ite_eq_left ht] using hv
      exact hv'.symm
    · intro he
      by_contra hn
      have hv' : (0 : Fin 2) = ε := by simpa only [ite_eq_right hn] using hv
      have hz : (0 : Fin 2) = 1 := hv'.trans he
      norm_num at hz
  simpa only [decide_eq_true_eq] using (h.upper_agree (f i) (f j) (hf hij)).trans he

theorem triangle_reindex (φ : L.Formula (Fin (n+m))) (P : Set (Fin m → M))
    (a : ℕ → Fin n → M) (b c : ℕ → Fin m → M) (h : Triangle φ P a b c)
    (f : ℕ → ℕ) (hf : StrictMono f) :
    Triangle φ P (a ∘ f) (b ∘ f) (c ∘ f) := by
  refine ⟨fun i => h.positive (f i),fun i => h.negative (f i),?_,?_,?_⟩
  · intro i j hij
    exact h.lower_true (f i) (f j) (hf.monotone hij)
  · intro i j hij
    exact h.lower_false (f i) (f j) (hf.monotone hij)
  · intro i j hij
    exact h.upper_agree (f i) (f j) (hf hij)

theorem true_upper_order_pattern (φ : L.Formula (Fin (n+m))) (P : Set (Fin m → M))
    (a : ℕ → Fin n → M) (b c : ℕ → Fin m → M) (h : Triangle φ P a b c)
    (hu : ∀ i j, i < j → Truth φ (a i) (b j)) (k : ℕ) :
    OrderPattern φ (fun i : Fin k => a i.val) (fun j : Fin k => c j.val) := by
  intro i j
  constructor
  · intro ht
    by_contra hn
    exact h.lower_false i.val j.val (Nat.le_of_not_gt hn) ht
  · intro hij
    exact (h.upper_agree i.val j.val hij).mp (hu i.val j.val hij)

theorem false_upper_order_pattern (φ : L.Formula (Fin (n+m))) (P : Set (Fin m → M))
    (a : ℕ → Fin n → M) (b c : ℕ → Fin m → M) (h : Triangle φ P a b c)
    (hu : ∀ i j, i < j → ¬ Truth φ (a i) (b j)) (k : ℕ) :
    OrderPattern φ (fun i : Fin k => a (k-i.val))
      (fun j : Fin k => b (k+1-j.val)) := by
  intro i j
  constructor
  · intro ht
    have hle : k+1-j.val ≤ k-i.val := by
      by_contra hn
      exact hu _ _ (Nat.lt_of_not_ge hn) ht
    have hi := i.isLt
    have hj := j.isLt
    change i.val < j.val
    omega
  · intro hij
    apply h.lower_true
    have hi := i.isLt
    have hj := j.isLt
    change i.val < j.val at hij
    omega

theorem triangle_finite_patterns (φ : L.Formula (Fin (n+m))) (P : Set (Fin m → M))
    (a : ℕ → Fin n → M) (b c : ℕ → Fin m → M) (h : Triangle φ P a b c) (k : ℕ) :
    ∃ a' : Fin k → Fin n → M, ∃ b' : Fin k → Fin m → M, OrderPattern φ a' b' := by
  obtain ⟨f,hf,ε,hε⟩ := homogeneous_upper φ P a b c h
  have hr := triangle_reindex φ P a b c h f hf
  cases ε with
  | false =>
    exact ⟨_,_,false_upper_order_pattern φ P (a ∘ f) (b ∘ f) (c ∘ f) hr
      (fun i j hij ht => Bool.false_ne_true ((hε i j hij).mp ht)) k⟩
  | true =>
    exact ⟨_,_,true_upper_order_pattern φ P (a ∘ f) (b ∘ f) (c ∘ f) hr
      (fun i j hij => (hε i j hij).mpr rfl) k⟩

theorem finite_separation [Nonempty M] (T : L.Theory) [M ⊨ T]
    (φ : L.Formula (Fin (n+m))) (hs : StableFormula T φ)
    (P : Set (Fin m → M)) (hP : IsLocalType φ P) :
    ∃ k, ∃ a : Fin k → Fin n → M, Separates φ P a := by
  by_contra hn
  obtain ⟨a,b,c,h⟩ := exists_triangle φ P hP hn
  apply hs
  intro k hk
  obtain ⟨a',b',hp⟩ := triangle_finite_patterns φ P a b c h k
  exact hasFinitePattern_of_model T φ k a' b' hp

end
end Lemmatheca.ModelTheory.StableDefinability
