import Lemmatheca.QuantifierElimination.QuantifierEliminationCriterion
import Mathlib.ModelTheory.Order
import Mathlib.Data.Finset.Max
import Mathlib.Data.Set.Finite.Basic
import Lemmatheca.FirstOrderStructures.FirstOrderSemantics

open Lemmatheca.MathematicalLogic

/-! Quantifier elimination in the equality and strict-order languages.

`Formula o n` is ordinary relational first-order syntax with a declared tuple of
`n` variables. Quantification appends one scoped slot. There are no function or
constant symbols. `o = false` gives equality alone and `o = true` adds strict order.
The elimination proof classifies finite atomic patterns, rather than using
countable categoricity or any back-and-forth theorem.
-/

namespace Lemmatheca.ModelTheory.QuantifierElimination

universe u v

def Relation (ordered : Bool) := if ordered then Unit else Empty

instance (o : Bool) : Fintype (Relation o) := by
  cases o <;> simp only [Relation, Bool.false_eq_true, ↓reduceIte] <;> infer_instance

instance (o : Bool) : DecidableEq (Relation o) := by
  cases o <;> simp only [Relation, Bool.false_eq_true, ↓reduceIte] <;> infer_instance

instance : IsEmpty (Relation false) := by simp only [Relation, Bool.false_eq_true, ↓reduceIte]; infer_instance

abbrev Atom (o : Bool) (n : ℕ) := (Fin n × Fin n) ⊕ (Relation o × Fin n × Fin n)

inductive Formula (o : Bool) : ℕ → Type
  | bot {n : ℕ} : Formula o n
  | atom {n : ℕ} : Atom o n → Formula o n
  | imp {n : ℕ} : Formula o n → Formula o n → Formula o n
  | ex {n : ℕ} : Formula o (n + 1) → Formula o n
  deriving DecidableEq

namespace Formula

def neg {o n} (φ : Formula o n) : Formula o n := φ.imp .bot
def top {o n} : Formula o n := (.bot : Formula o n).neg
def conj {o n} (φ ψ : Formula o n) : Formula o n := (φ.imp ψ.neg).neg
def disj {o n} (φ ψ : Formula o n) : Formula o n := φ.neg.imp ψ
def all {o n} (φ : Formula o (n + 1)) : Formula o n := φ.neg.ex.neg

inductive IsQF {o : Bool} : ∀ {n : ℕ}, Formula o n → Prop
  | bot {n} : IsQF (.bot : Formula o n)
  | atom {n} (a : Atom o n) : IsQF (.atom a)
  | imp {n} {φ ψ : Formula o n} : IsQF φ → IsQF ψ → IsQF (φ.imp ψ)

def realizeAtom {o n} {M : Type u} (r : M → M → Prop) (a : Atom o n)
    (x : Fin n → M) : Prop :=
  match a with
  | .inl (i, j) => x i = x j
  | .inr (_, i, j) => r (x i) (x j)

def Realize {o : Bool} {M : Type u} (r : M → M → Prop) :
    {n : ℕ} → Formula o n → (Fin n → M) → Prop
  | _, .bot, _ => False
  | _, .atom a, x => realizeAtom r a x
  | _, .imp φ ψ, x => Realize r φ x → Realize r ψ x
  | _, .ex φ, x => ∃ y, Realize r φ (Fin.snoc x y)

@[simp] theorem realize_neg {o n} {M : Type u} (r : M → M → Prop)
    (φ : Formula o n) (x : Fin n → M) :
    φ.neg.Realize r x ↔ ¬ φ.Realize r x := Iff.rfl

@[simp] theorem realize_top {o n} {M : Type u} (r : M → M → Prop) (x : Fin n → M) :
    (top : Formula o n).Realize r x := fun h => h

@[simp] theorem realize_conj {o n} {M : Type u} (r : M → M → Prop)
    (φ ψ : Formula o n) (x : Fin n → M) :
    (φ.conj ψ).Realize r x ↔ φ.Realize r x ∧ ψ.Realize r x := by
  classical
  simp only [conj, Realize, neg]
  tauto

@[simp] theorem realize_disj {o n} {M : Type u} (r : M → M → Prop)
    (φ ψ : Formula o n) (x : Fin n → M) :
    (φ.disj ψ).Realize r x ↔ φ.Realize r x ∨ ψ.Realize r x := by
  classical
  simp only [disj, neg, Realize]
  tauto

def andList {o n} : List (Formula o n) → Formula o n
  | [] => top
  | φ :: l => φ.conj (andList l)

def orList {o n} : List (Formula o n) → Formula o n
  | [] => .bot
  | φ :: l => φ.disj (orList l)

@[simp] theorem realize_andList {o n} {M : Type u} (r : M → M → Prop)
    (l : List (Formula o n)) (x : Fin n → M) :
    (andList l).Realize r x ↔ ∀ φ ∈ l, φ.Realize r x := by
  induction l with
  | nil => simp [andList]
  | cons φ l ih => simp [andList, ih]

@[simp] theorem realize_orList {o n} {M : Type u} (r : M → M → Prop)
    (l : List (Formula o n)) (x : Fin n → M) :
    (orList l).Realize r x ↔ ∃ φ ∈ l, φ.Realize r x := by
  induction l with
  | nil => simp [orList, Realize]
  | cons φ l ih => simp [orList, ih]

theorem isQF_andList {o n} (l : List (Formula o n)) (h : ∀ φ ∈ l, φ.IsQF) :
    (andList l).IsQF := by
  induction l with
  | nil => exact .imp .bot .bot
  | cons φ l ih =>
    exact .imp (.imp (h φ (by simp)) (.imp (ih (fun ψ hψ => h ψ (List.mem_cons_of_mem _ hψ))) .bot)) .bot

theorem isQF_orList {o n} (l : List (Formula o n)) (h : ∀ φ ∈ l, φ.IsQF) :
    (orList l).IsQF := by
  induction l with
  | nil => exact .bot
  | cons φ l ih =>
    exact .imp (.imp (h φ (by simp)) .bot) (ih (fun ψ hψ => h ψ (List.mem_cons_of_mem _ hψ)))

end Formula

open Formula

/-- Two finite tuples have the same atomic equality/order pattern. -/
def Similar {o : Bool} {n : ℕ} {M : Type u} {N : Type v} (r : M → M → Prop) (s : N → N → Prop)
    (x : Fin n → M) (y : Fin n → N) : Prop :=
  ∀ a : Atom o n, realizeAtom r a x ↔ realizeAtom s a y

theorem similar_refl {o n} {M : Type u} (r : M → M → Prop) (x : Fin n → M) :
    Similar (o := o) r r x x := fun _ => Iff.rfl

theorem Similar.symm {o n} {M : Type u} {N : Type v}
    {r : M → M → Prop} {s : N → N → Prop} {x : Fin n → M} {y : Fin n → N}
    (h : Similar (o := o) r s x y) : Similar (o := o) s r y x := fun a => (h a).symm

theorem Similar.eq {o n} {M : Type u} {N : Type v}
    {r : M → M → Prop} {s : N → N → Prop} {x : Fin n → M} {y : Fin n → N}
    (h : Similar (o := o) r s x y) (i j : Fin n) : x i = x j ↔ y i = y j :=
  h (.inl (i, j))

theorem Similar.lt {n} {M : Type u} {N : Type v}
    {r : M → M → Prop} {s : N → N → Prop} {x : Fin n → M} {y : Fin n → N}
    (h : Similar (o := true) r s x y) (i j : Fin n) : r (x i) (x j) ↔ s (y i) (y j) :=
  h (.inr ((), i, j))

theorem similar_snoc {o n} {M : Type u} {N : Type v}
    {r : M → M → Prop} {s : N → N → Prop} {x : Fin n → M} {y : Fin n → N}
    (h : Similar (o := o) r s x y) (a : M) (b : N)
    (he : ∀ i, x i = a ↔ y i = b)
    (hl : ∀ (_ : Relation o) i, r (x i) a ↔ s (y i) b)
    (hr : ∀ (_ : Relation o) i, r a (x i) ↔ s b (y i))
    (hs : ∀ _ : Relation o, r a a ↔ s b b) :
    Similar (o := o) r s (Fin.snoc x a) (Fin.snoc y b) := by
  intro z
  rcases z with ⟨i, j⟩ | ⟨q, i, j⟩
  · induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => simp [realizeAtom]
      | cast j => simpa [realizeAtom, eq_comm] using he j
    | cast i =>
      induction j using Fin.lastCases with
      | last => simpa [realizeAtom] using he i
      | cast j => simpa [realizeAtom] using h.eq i j
  · induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => simpa [realizeAtom] using hs q
      | cast j => simpa [realizeAtom] using hr q j
    | cast i =>
      induction j using Fin.lastCases with
      | last => simpa [realizeAtom] using hl q i
      | cast j => simpa [realizeAtom] using h (.inr (q, i, j))

/-- Every one-element extension of a tuple pattern can be matched. -/
def Extends {o : Bool} {M : Type u} {N : Type v} (r : M → M → Prop) (s : N → N → Prop) : Prop :=
  ∀ (n : ℕ) (x : Fin n → M) (y : Fin n → N), Similar (o := o) r s x y →
    ∀ a : M, ∃ b : N, Similar (o := o) r s (Fin.snoc x a) (Fin.snoc y b)

theorem realize_of_patterns {o} {M : Type u} {N : Type v}
    {r : M → M → Prop} {s : N → N → Prop}
    (hMN : Extends (o := o) r s) (hNM : Extends (o := o) s r)
    {n} (φ : Formula o n) {x : Fin n → M} {y : Fin n → N}
    (h : Similar (o := o) r s x y) : φ.Realize r x ↔ φ.Realize s y := by
  induction φ with
  | bot => rfl
  | atom a => exact h a
  | imp φ ψ ihφ ihψ => exact imp_congr (ihφ h) (ihψ h)
  | ex φ ih =>
    constructor
    · rintro ⟨a, ha⟩
      obtain ⟨b, hb⟩ := hMN _ x y h a
      exact ⟨b, (ih hb).mp ha⟩
    · rintro ⟨b, hb⟩
      obtain ⟨a, ha⟩ := hNM _ y x h.symm b
      exact ⟨a, (ih ha.symm).mpr hb⟩

theorem tuple_pattern_exists {o} {M : Type u} {N : Type v}
    {r : M → M → Prop} {s : N → N → Prop} (hMN : Extends (o := o) r s)
    (n : ℕ) (x : Fin n → M) : ∃ y : Fin n → N, Similar (o := o) r s x y := by
  induction n with
  | zero =>
    refine ⟨Fin.elim0, ?_⟩
    intro a
    rcases a with ⟨i, _⟩ | ⟨_, i, _⟩ <;> exact Fin.elim0 i
  | succ n ih =>
    obtain ⟨y, hy⟩ := ih (Fin.init x)
    obtain ⟨b, hb⟩ := hMN n (Fin.init x) y hy (x (Fin.last n))
    exact ⟨Fin.snoc y b, by simpa only [Fin.snoc_init_self] using hb⟩

noncomputable def pattern {o n} {M : Type u} (r : M → M → Prop) (x : Fin n → M) :
    Atom o n → Bool := by
  classical
  exact fun a => decide (realizeAtom r a x)

noncomputable def patternFormula {o n} (p : Atom o n → Bool) : Formula o n := by
  classical
  exact andList (Finset.univ.toList.map fun a =>
    if p a then Formula.atom a else (Formula.atom a).neg)

theorem patternFormula_isQF {o n} (p : Atom o n → Bool) : (patternFormula p).IsQF := by
  classical
  apply isQF_andList
  intro φ hφ
  obtain ⟨a, _, rfl⟩ := List.mem_map.mp hφ
  split
  · exact IsQF.atom a
  · exact IsQF.imp (IsQF.atom a) IsQF.bot

theorem realize_patternFormula {o n} {M : Type u} (r : M → M → Prop)
    (p : Atom o n → Bool) (x : Fin n → M) :
    (patternFormula p).Realize r x ↔ pattern r x = p := by
  classical
  rw [patternFormula, realize_andList]
  constructor
  · intro h
    funext a
    have ha := h _ (List.mem_map.mpr ⟨a, by simp, rfl⟩)
    cases hp : p a <;> simp [hp, pattern, Realize] at ha ⊢ <;> exact ha
  · intro h φ hφ
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hφ
    have ha := congrFun h a
    cases hp : p a <;> simp [hp, pattern, Realize] at ha ⊢ <;> exact ha

/-- Select exactly the finitely many atomic patterns on which the original formula holds
in a fixed reference model. This is a finite syntactic formula, not a semantic predicate. -/
noncomputable def eliminate {o n} {C : Type u} (r : C → C → Prop)
    (φ : Formula o n) : Formula o n := by
  classical
  exact orList ((Finset.univ.filter fun p : Atom o n → Bool =>
    ∃ x : Fin n → C, pattern r x = p ∧ φ.Realize r x).toList.map patternFormula)

theorem eliminate_isQF {o n} {C : Type u} (r : C → C → Prop) (φ : Formula o n) :
    (eliminate r φ).IsQF := by
  classical
  apply isQF_orList
  intro ψ hψ
  obtain ⟨p, _, rfl⟩ := List.mem_map.mp hψ
  exact patternFormula_isQF p

theorem eliminate_correct {o n} {C : Type u} {M : Type v}
    (r : C → C → Prop) (s : M → M → Prop)
    (hCM : Extends (o := o) r s) (hMC : Extends (o := o) s r)
    (φ : Formula o n) (x : Fin n → M) :
    (eliminate r φ).Realize s x ↔ φ.Realize s x := by
  classical
  simp only [eliminate, realize_orList, List.mem_map, Finset.mem_toList,
    Finset.mem_filter, Finset.mem_univ, true_and, exists_exists_and_eq_and]
  constructor
  · rintro ⟨p, ⟨y, hy, hφ⟩, hp⟩
    have he := (realize_patternFormula s p x).mp hp
    have hs : Similar (o := o) r s y x := by
      intro a
      have h := congrFun (hy.trans he.symm) a
      exact decide_eq_decide.mp h
    exact (realize_of_patterns hCM hMC φ hs).mp hφ
  · intro hφ
    obtain ⟨y, hy⟩ := tuple_pattern_exists hMC n x
    refine ⟨pattern s x, ⟨y, ?_, (realize_of_patterns hMC hCM φ hy).mp hφ⟩, ?_⟩
    · funext a
      exact Bool.decide_congr (hy a).symm
    · exact (realize_patternFormula s _ x).mpr rfl

def noRelation {M : Type u} : M → M → Prop := fun _ _ => False

theorem equality_extends {M : Type u} {N : Type v} [Infinite N] :
    Extends (o := false) (noRelation (M := M)) (noRelation (M := N)) := by
  classical
  intro n x y h a
  by_cases ha : ∃ i, x i = a
  · obtain ⟨i, rfl⟩ := ha
    refine ⟨y i, similar_snoc h _ _ (fun j => h.eq j i) ?_ ?_ ?_⟩
    all_goals intro q; exact isEmptyElim q
  · obtain ⟨b, _, hb⟩ := Set.Infinite.exists_notMem_finite (Set.infinite_univ : (Set.univ : Set N).Infinite) (Set.finite_range y)
    refine ⟨b, similar_snoc h _ _ ?_ ?_ ?_ ?_⟩
    · intro i
      exact iff_of_false (fun hi => ha ⟨i, hi⟩) (fun hi => hb ⟨i, hi⟩)
    all_goals intro q; exact isEmptyElim q

/-- All four finite-bound cases: two nonempty sides, either one side, or no bounds. -/
theorem finite_bounds {M : Type u} [LinearOrder M] [DenselyOrdered M]
    [NoMinOrder M] [NoMaxOrder M] [Nonempty M]
    (l u : Finset M) (h : ∀ a ∈ l, ∀ b ∈ u, a < b) :
    ∃ x : M, (∀ a ∈ l, a < x) ∧ ∀ b ∈ u, x < b := by
  classical
  by_cases hl : l.Nonempty
  · by_cases hu : u.Nonempty
    · obtain ⟨x, hxl, hxu⟩ := exists_between (h _ (l.max'_mem hl) _ (u.min'_mem hu))
      exact ⟨x, fun a ha => (l.le_max' a ha).trans_lt hxl,
        fun b hb => hxu.trans_le (u.min'_le b hb)⟩
    · obtain ⟨x, hx⟩ := exists_gt (l.max' hl)
      exact ⟨x, fun a ha => (l.le_max' a ha).trans_lt hx, by simp [Finset.not_nonempty_iff_eq_empty.mp hu]⟩
  · by_cases hu : u.Nonempty
    · obtain ⟨x, hx⟩ := exists_lt (u.min' hu)
      exact ⟨x, by simp [Finset.not_nonempty_iff_eq_empty.mp hl],
        fun b hb => hx.trans_le (u.min'_le b hb)⟩
    · exact ⟨Classical.choice inferInstance, by simp [Finset.not_nonempty_iff_eq_empty.mp hl],
        by simp [Finset.not_nonempty_iff_eq_empty.mp hu]⟩

theorem dlo_extends {M : Type u} {N : Type v}
    [LinearOrder M] [LinearOrder N] [DenselyOrdered N]
    [NoMinOrder N] [NoMaxOrder N] [Nonempty N] :
    Extends (o := true) (fun a b : M => a < b) (fun a b : N => a < b) := by
  classical
  intro n x y h a
  by_cases ha : ∃ i, x i = a
  · obtain ⟨i, rfl⟩ := ha
    exact ⟨y i, similar_snoc h _ _ (fun j => h.eq j i)
      (fun _ j => h.lt j i) (fun _ j => h.lt i j) (fun _ => by simp)⟩
  · let l := (Finset.univ.filter fun i => x i < a).image y
    let u := (Finset.univ.filter fun i => a < x i).image y
    have hcut : ∀ b ∈ l, ∀ c ∈ u, b < c := by
      intro b hb c hc
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hb
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hc
      exact (h.lt i j).mp (lt_trans (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2)
    obtain ⟨b, hbl, hbu⟩ := finite_bounds l u hcut
    have hleft (i : Fin n) : x i < a ↔ y i < b := by
      constructor
      · intro hi
        exact hbl _ (Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩, rfl⟩)
      · intro hi
        by_contra hia
        have hai : a < x i := lt_of_le_of_ne (le_of_not_gt hia) (Ne.symm (fun he => ha ⟨i, he⟩))
        have hbi := hbu _ (Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hai⟩, rfl⟩)
        exact (lt_asymm hi hbi)
    have hright (i : Fin n) : a < x i ↔ b < y i := by
      constructor
      · intro hi
        exact hbu _ (Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩, rfl⟩)
      · intro hi
        by_contra hai
        have hia : x i < a := lt_of_le_of_ne (le_of_not_gt hai) (fun he => ha ⟨i, he⟩)
        exact lt_asymm hi ((hleft i).mp hia)
    refine ⟨b, similar_snoc h a b ?_ (fun _ i => hleft i) (fun _ i => hright i) (fun _ => by simp)⟩
    intro i
    constructor
    · intro hi
      exact (ha ⟨i, hi⟩).elim
    · intro hi
      rcases lt_or_gt_of_ne (show x i ≠ a from fun he => ha ⟨i, he⟩) with hia | hai
      · exact (ne_of_lt ((hleft i).mp hia) hi).elim
      · exact (ne_of_gt ((hright i).mp hai) hi).elim

noncomputable def equalityEliminate {n} (φ : Formula false n) : Formula false n :=
  eliminate (noRelation (M := ℕ)) φ

noncomputable def dloEliminate {n} (φ : Formula true n) : Formula true n :=
  eliminate (fun a b : ℚ => a < b) φ

theorem equality_quantifier_elimination {n} (φ : Formula false n) :
    (equalityEliminate φ).IsQF ∧
      ∀ (M : Type u) [Infinite M] (x : Fin n → M),
        (equalityEliminate φ).Realize noRelation x ↔ φ.Realize noRelation x := by
  exact ⟨eliminate_isQF _ φ, fun _ _ x =>
    eliminate_correct _ _ equality_extends equality_extends φ x⟩

theorem dlo_quantifier_elimination {n} (φ : Formula true n) :
    (dloEliminate φ).IsQF ∧
      ∀ (M : Type u) [LinearOrder M] [DenselyOrdered M] [NoMinOrder M] [NoMaxOrder M]
        [Nonempty M] (x : Fin n → M),
        (dloEliminate φ).Realize (fun a b => a < b) x ↔ φ.Realize (fun a b => a < b) x := by
  exact ⟨eliminate_isQF _ φ, fun _ _ _ _ _ _ x =>
    eliminate_correct _ _ dlo_extends dlo_extends φ x⟩

theorem equality_sentence_agreement {M : Type u} {N : Type v} [Infinite M] [Infinite N]
    (φ : Formula false 0) : φ.Realize (noRelation (M := M)) Fin.elim0 ↔
      φ.Realize (noRelation (M := N)) Fin.elim0 := by
  apply realize_of_patterns equality_extends equality_extends
  intro a
  rcases a with ⟨i, _⟩ | ⟨_, i, _⟩ <;> exact Fin.elim0 i

theorem dlo_sentence_agreement {M : Type u} {N : Type v}
    [LinearOrder M] [DenselyOrdered M] [NoMinOrder M] [NoMaxOrder M] [Nonempty M]
    [LinearOrder N] [DenselyOrdered N] [NoMinOrder N] [NoMaxOrder N] [Nonempty N]
    (φ : Formula true 0) : φ.Realize (fun a b : M => a < b) Fin.elim0 ↔
      φ.Realize (fun a b : N => a < b) Fin.elim0 := by
  apply realize_of_patterns dlo_extends dlo_extends
  intro a
  rcases a with ⟨i, _⟩ | ⟨_, i, _⟩ <;> exact Fin.elim0 i

theorem equality_injection_elementary {M : Type u} {N : Type v} [Infinite M] [Infinite N]
    (f : M → N) (hf : Function.Injective f) {n} (φ : Formula false n) (x : Fin n → M) :
    φ.Realize noRelation x ↔ φ.Realize noRelation (f ∘ x) := by
  apply realize_of_patterns equality_extends equality_extends
  rintro (⟨i, j⟩ | ⟨r, _, _⟩)
  · exact hf.eq_iff.symm
  · exact isEmptyElim r

theorem dlo_embedding_elementary {M : Type u} {N : Type v}
    [LinearOrder M] [DenselyOrdered M] [NoMinOrder M] [NoMaxOrder M] [Nonempty M]
    [LinearOrder N] [DenselyOrdered N] [NoMinOrder N] [NoMaxOrder N] [Nonempty N]
    (f : M ↪o N) {n} (φ : Formula true n) (x : Fin n → M) :
    φ.Realize (fun a b => a < b) x ↔ φ.Realize (fun a b => a < b) (f ∘ x) := by
  apply realize_of_patterns dlo_extends dlo_extends
  rintro (⟨i, j⟩ | ⟨_, i, j⟩)
  · exact f.injective.eq_iff.symm
  · exact (f.lt_iff_lt).symm

/-- Equivalence modulo an explicitly given class of nonempty relational models. -/
def Equivalent {o n} (K : (M : Type u) → (M → M → Prop) → Prop)
    (φ ψ : Formula o n) : Prop :=
  ∀ (M : Type u) (r : M → M → Prop), K M r → ∀ x, φ.Realize r x ↔ ψ.Realize r x

def HasQE {o : Bool} (K : (M : Type u) → (M → M → Prop) → Prop) : Prop :=
  ∀ (n : ℕ) (φ : Formula o n), ∃ ψ, ψ.IsQF ∧ Equivalent K φ ψ

/-- The same definition for the shared general first-order syntax. Listing every
available variable as a scoped slot covers any finite free-variable list as well. -/
def HasQuantifierElimination {L : FirstOrder.Language} (T : L.Theory) : Prop :=
  ∀ (n : ℕ) (φ : L.BoundedFormula Empty n), ∃ ψ, FirstOrder.Language.BoundedFormula.IsQF ψ ∧ FirstOrder.Language.Theory.Iff T φ ψ

theorem qe_of_one_existential {o : Bool}
    (K : (M : Type u) → (M → M → Prop) → Prop)
    (h : ∀ (n : ℕ) (φ : Formula o (n + 1)), φ.IsQF →
      ∃ ψ, ψ.IsQF ∧ Equivalent K φ.ex ψ) : HasQE (o := o) K := by
  intro n φ
  induction φ with
  | bot => exact ⟨.bot, .bot, fun _ _ _ _ => Iff.rfl⟩
  | atom a => exact ⟨.atom a, .atom a, fun _ _ _ _ => Iff.rfl⟩
  | imp φ ψ ihφ ihψ =>
    obtain ⟨φ', hφ', hφ⟩ := ihφ
    obtain ⟨ψ', hψ', hψ⟩ := ihψ
    refine ⟨φ'.imp ψ', .imp hφ' hψ', fun M r hM x => ?_⟩
    change (φ.Realize r x → ψ.Realize r x) ↔ (φ'.Realize r x → ψ'.Realize r x)
    exact imp_congr (hφ M r hM x) (hψ M r hM x)
  | ex φ ih =>
    obtain ⟨φ', hφ', hφ⟩ := ih
    obtain ⟨ψ, hψ, he⟩ := h _ φ' hφ'
    refine ⟨ψ, hψ, fun M r hM x => ?_⟩
    exact (exists_congr fun y => hφ M r hM (Fin.snoc x y)).trans (he M r hM x)

theorem qf_pattern_invariance {o n} {M : Type u} {N : Type v}
    {r : M → M → Prop} {s : N → N → Prop}
    {φ : Formula o n} (hφ : φ.IsQF) {x : Fin n → M} {y : Fin n → N}
    (h : Similar (o := o) r s x y) : φ.Realize r x ↔ φ.Realize s y := by
  induction hφ with
  | bot => rfl
  | atom a => exact h a
  | imp _ _ ihφ ihψ => exact imp_congr ihφ ihψ

theorem existential_distributes {M : Type u} {ι : Type v}
    (P : ι → M → Prop) : (∃ x, ∃ i, P i x) ↔ ∃ i, ∃ x, P i x :=
  exists_comm

theorem equality_witness_substitution {M : Type u} (a : M) (P : M → Prop) :
    (∃ x, x = a ∧ P x) ↔ P a := by simp

theorem equality_finite_exclusions {M : Type u} [Infinite M]
    (s : Finset M) (C : Prop) : (∃ x, C ∧ x ∉ s) ↔ C := by
  classical
  constructor
  · rintro ⟨_, h, _⟩; exact h
  · intro h
    obtain ⟨x, hx⟩ := s.exists_notMem
    exact ⟨x, h, hx⟩

theorem dlo_negated_atoms {M : Type u} [LinearOrder M] (a b : M) :
    (a ≠ b ↔ a < b ∨ b < a) ∧ (¬a < b ↔ a = b ∨ b < a) := by
  constructor
  · exact ne_iff_lt_or_gt
  · simpa only [eq_comm] using (not_lt : ¬a < b ↔ b ≤ a).trans le_iff_eq_or_lt

theorem dlo_clause_elimination {M : Type u} [LinearOrder M] [DenselyOrdered M]
    [NoMinOrder M] [NoMaxOrder M] [Nonempty M]
    (l u : Finset M) (C : Prop) :
    (∃ x, C ∧ (∀ a ∈ l, a < x) ∧ ∀ b ∈ u, x < b) ↔
      C ∧ ∀ a ∈ l, ∀ b ∈ u, a < b := by
  constructor
  · rintro ⟨x, hC, hl, hu⟩
    exact ⟨hC, fun a ha b hb => (hl a ha).trans (hu b hb)⟩
  · rintro ⟨hC, h⟩
    obtain ⟨x, hl, hu⟩ := finite_bounds l u h
    exact ⟨x, hC, hl, hu⟩

theorem equality_unary_finite_or_cofinite {M : Type u} [Infinite M]
    {n : ℕ} (φ : Formula false (n + 1)) (a : Fin n → M) :
    Set.Finite {x | φ.Realize noRelation (Fin.snoc a x)} ∨
      Set.Finite {x | ¬φ.Realize noRelation (Fin.snoc a x)} := by
  classical
  obtain ⟨b, hb⟩ := (Set.finite_range a).exists_notMem
  have agree (x : M) (hx : x ∉ Set.range a) :
      φ.Realize noRelation (Fin.snoc a x) ↔ φ.Realize noRelation (Fin.snoc a b) := by
    apply realize_of_patterns equality_extends equality_extends
    apply similar_snoc (similar_refl noRelation a) x b
    · intro i
      exact iff_of_false (fun h => hx ⟨i, h⟩) (fun h => hb ⟨i, h⟩)
    all_goals intro q; exact isEmptyElim q
  by_cases h : φ.Realize noRelation (Fin.snoc a b)
  · right
    apply (Set.finite_range a).subset
    intro x hx
    by_contra hxa
    exact hx ((agree x hxa).mpr h)
  · left
    apply (Set.finite_range a).subset
    intro x hx
    by_contra hxa
    exact h ((agree x hxa).mp hx)

/-- An interval can be bounded, a ray, or the whole domain. -/
inductive Cell (M : Type u)
  | empty
  | point (a : M)
  | interval (lower upper : Option M)
  deriving DecidableEq

def Cell.realize {M : Type u} [LT M] : Cell M → Set M
  | .empty => ∅
  | .point a => {a}
  | .interval l u => {x | (∀ a ∈ l, a < x) ∧ ∀ b ∈ u, x < b}

/-- The unary order pattern relative to the listed parameters. -/
def Cell.Supported {M : Type u} (A : Set M) : Cell M → Prop
  | .empty => True
  | .point a => a ∈ A
  | .interval l u => (∀ a ∈ l, a ∈ A) ∧ ∀ b ∈ u, b ∈ A

def SameCell {M : Type u} [LT M] {n : ℕ} (a : Fin n → M) (x y : M) : Prop :=
  (∀ i, a i = x ↔ a i = y) ∧
    (∀ i, a i < x ↔ a i < y) ∧ ∀ i, x < a i ↔ y < a i

theorem sameCell_similarity {M : Type u} [LinearOrder M] {n : ℕ}
    (a : Fin n → M) {x y : M} (h : SameCell a x y) :
    Similar (o := true) (fun a b : M => a < b) (fun a b : M => a < b)
      (Fin.snoc a x) (Fin.snoc a y) :=
  similar_snoc (similar_refl _ a) x y h.1 (fun _ => h.2.1) (fun _ => h.2.2) (fun _ => by simp)

/-- Each realizable unary pattern is a singleton or one open interval/ray. -/
theorem sameCell_is_interval {M : Type u} [LinearOrder M] {n : ℕ}
    (a : Fin n → M) (x : M) :
    ∃ c : Cell M, c.Supported (Set.range a) ∧ c.realize = {y | SameCell a x y} := by
  classical
  by_cases he : ∃ i, a i = x
  · refine ⟨.point x, he, ?_⟩
    ext y
    simp only [Cell.realize, Set.mem_singleton_iff, Set.mem_ofPred_eq]
    constructor
    · intro h
      subst y
      exact ⟨fun _ => Iff.rfl, fun _ => Iff.rfl, fun _ => Iff.rfl⟩
    · intro h
      obtain ⟨i, hi⟩ := he
      exact ((h.1 i).mp hi).symm.trans hi
  · let l := (Finset.univ.filter fun i => a i < x).image a
    let u := (Finset.univ.filter fun i => x < a i).image a
    let lo : Option M := if hl : l.Nonempty then some (l.max' hl) else none
    let up : Option M := if hu : u.Nonempty then some (u.min' hu) else none
    have hlo (y : M) : (∀ b ∈ lo, b < y) ↔ ∀ b ∈ l, b < y := by
      dsimp [lo]
      split
      · rename_i hl
        simp only [Option.mem_some_iff, forall_eq']
        exact ⟨fun h b hb => (l.le_max' b hb).trans_lt h, fun h => h _ (l.max'_mem hl)⟩
      · rename_i hl
        simp [Finset.not_nonempty_iff_eq_empty.mp hl]
    have hup (y : M) : (∀ b ∈ up, y < b) ↔ ∀ b ∈ u, y < b := by
      dsimp [up]
      split
      · rename_i hu
        simp only [Option.mem_some_iff, forall_eq']
        exact ⟨fun h b hb => h.trans_le (u.min'_le b hb), fun h => h _ (u.min'_mem hu)⟩
      · rename_i hu
        simp [Finset.not_nonempty_iff_eq_empty.mp hu]
    have hsupport : (Cell.interval lo up).Supported (Set.range a) := by
      constructor
      · intro b hb
        dsimp [lo] at hb
        split at hb
        · rename_i hl
          have hbl : b ∈ l := by
            have heq : l.max' hl = b := Option.mem_some_iff.mp hb
            exact heq ▸ l.max'_mem hl
          obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hbl
          exact ⟨i, hi⟩
        · simp at hb
      · intro b hb
        dsimp [up] at hb
        split at hb
        · rename_i hu
          have hbu : b ∈ u := by
            have heq : u.min' hu = b := Option.mem_some_iff.mp hb
            exact heq ▸ u.min'_mem hu
          obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hbu
          exact ⟨i, hi⟩
        · simp at hb
    refine ⟨.interval lo up, hsupport, ?_⟩
    ext y
    change ((∀ b ∈ lo, b < y) ∧ ∀ b ∈ up, y < b) ↔ SameCell a x y
    rw [hlo, hup]
    constructor
    · rintro ⟨hl, hu⟩
      have hl' (i : Fin n) (hi : a i < x) : a i < y :=
        hl _ (Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩, rfl⟩)
      have hu' (i : Fin n) (hi : x < a i) : y < a i :=
        hu _ (Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩, rfl⟩)
      refine ⟨?_, ?_, ?_⟩
      · intro i
        apply iff_of_false (fun h => he ⟨i, h⟩)
        intro h
        rcases lt_or_gt_of_ne (show a i ≠ x from fun h => he ⟨i, h⟩) with hi | hi
        · exact ne_of_lt (hl' i hi) h
        · exact ne_of_gt (hu' i hi) h
      · intro i
        constructor
        · exact hl' i
        · intro hi
          by_contra hn
          have hx : x < a i := lt_of_le_of_ne (le_of_not_gt hn) (Ne.symm (fun h => he ⟨i, h⟩))
          exact lt_asymm hi (hu' i hx)
      · intro i
        constructor
        · exact hu' i
        · intro hi
          by_contra hn
          have hx : a i < x := lt_of_le_of_ne (le_of_not_gt hn) (fun h => he ⟨i, h⟩)
          exact lt_asymm hi (hl' i hx)
    · rintro ⟨_, hl, hu⟩
      constructor
      · intro b hb
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hb
        exact (hl i).mp (Finset.mem_filter.mp hi).2
      · intro b hb
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hb
        exact (hu i).mp (Finset.mem_filter.mp hi).2

theorem dlo_unary_finite_union {M : Type u} [LinearOrder M] [DenselyOrdered M]
    [NoMinOrder M] [NoMaxOrder M] [Nonempty M]
    {n : ℕ} (φ : Formula true (n + 1)) (a : Fin n → M) :
    ∃ s : Finset (Cell M), (∀ c ∈ s, c.Supported (Set.range a)) ∧ {x | φ.Realize (fun a b : M => a < b) (Fin.snoc a x)} =
      {x | ∃ c ∈ s, x ∈ c.realize} := by
  classical
  let P := Atom true (n + 1) → Bool
  let good (p : P) := ∃ x, pattern (fun a b : M => a < b) (Fin.snoc a x) = p ∧
    φ.Realize (fun a b : M => a < b) (Fin.snoc a x)
  let representative (p : P) (hp : good p) := Classical.choose hp
  have rep_spec (p : P) (hp : good p) := Classical.choose_spec hp
  let cell (p : P) : Cell M := if hp : good p then
    Classical.choose (sameCell_is_interval a (representative p hp)) else .empty
  have cell_spec (p : P) (hp : good p) :
      (cell p).realize = {y | SameCell a (representative p hp) y} := by
    simp only [cell, dite_eq_left hp]
    exact (Classical.choose_spec (sameCell_is_interval a (representative p hp))).2
  refine ⟨Finset.univ.image cell, ?_, ?_⟩
  · intro c hc
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hc
    dsimp [cell]
    split
    · rename_i hp
      exact (Classical.choose_spec (sameCell_is_interval a (representative p hp))).1
    · trivial
  ext x
  constructor
  · intro hx
    let p : P := pattern (fun a b : M => a < b) (Fin.snoc a x)
    have hp : good p := ⟨x, rfl, hx⟩
    refine ⟨cell p, Finset.mem_image.mpr ⟨p, Finset.mem_univ _, rfl⟩, ?_⟩
    rw [cell_spec p hp]
    have hpat := congrFun (rep_spec p hp).1
    have hs : Similar (o := true) (fun a b : M => a < b) (fun a b : M => a < b)
        (Fin.snoc a (representative p hp)) (Fin.snoc a x) := by
      intro z
      exact decide_eq_decide.mp (hpat z)
    refine ⟨fun i => ?_, fun i => ?_, fun i => ?_⟩
    · simpa [realizeAtom] using hs.eq i.castSucc (Fin.last n)
    · simpa [realizeAtom] using hs.lt i.castSucc (Fin.last n)
    · simpa [realizeAtom] using hs.lt (Fin.last n) i.castSucc
  · rintro ⟨c, hc, hxc⟩
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hc
    by_cases hp : good p
    · rw [cell_spec p hp] at hxc
      exact (realize_of_patterns dlo_extends dlo_extends φ (sameCell_similarity a hxc)).mp
        (rep_spec p hp).2
    · simp [cell, hp, Cell.realize] at hxc

open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic.FirstOrderSyntax
open Lemmatheca.MathematicalLogic.FirstOrderSemantics

/-- Each interval or point has its displayed quantifier-free definition in the
shared strict-order syntax. The free names are the endpoint parameters. -/
def Cell.toBoundedFormula {M : Type u} : Cell M → binaryRelLanguage.BoundedFormula M 1
  | .empty => ⊥
  | .point a => .equal (.var (.inr 0)) (.var (.inl a))
  | .interval l u =>
    (match l with
      | none => ⊤
      | some a => .rel .rel ![.var (.inl a), .var (.inr 0)]) ⊓
    (match u with
      | none => ⊤
      | some b => .rel .rel ![.var (.inr 0), .var (.inl b)])

theorem Cell.toBoundedFormula_isQF {M : Type u} (c : Cell M) :
    c.toBoundedFormula.IsQF := by
  cases c with
  | empty => exact BoundedFormula.isQF_bot
  | point a => exact (BoundedFormula.IsAtomic.equal _ _).isQF
  | interval l u =>
    apply BoundedFormula.IsQF.inf
    · cases l
      · exact BoundedFormula.IsQF.top
      · exact (BoundedFormula.IsAtomic.rel _ _).isQF
    · cases u
      · exact BoundedFormula.IsQF.top
      · exact (BoundedFormula.IsAtomic.rel _ _).isQF

theorem Cell.toBoundedFormula_realize {M : Type u} [LT M] (c : Cell M) (x : M) :
    let : binaryRelLanguage.Structure M := binaryRelStructure M (fun a b => a < b)
    c.toBoundedFormula.Realize id ![x] ↔ x ∈ c.realize := by
  let : binaryRelLanguage.Structure M := binaryRelStructure M (fun a b => a < b)
  have hrel (v : Fin 2 → M) : Structure.RelMap (L := binaryRelLanguage) BinaryRelationSymbol.rel v ↔ v 0 < v 1 := Iff.rfl
  cases c with
  | empty => rfl
  | point a => rfl
  | interval l u =>
    cases l <;> cases u <;>
      simp [toBoundedFormula, Cell.realize, BoundedFormula.realize_inf,
        BoundedFormula.Realize, hrel]

theorem finite_cell_union_definable {M : Type u} [LT M] (s : Finset (Cell M)) :
    let : binaryRelLanguage.Structure M := binaryRelStructure M (fun a b => a < b)
    ∃ ψ : binaryRelLanguage.BoundedFormula M 1, ψ.IsQF ∧
      ∀ x : M, ψ.Realize id ![x] ↔ ∃ c ∈ s, x ∈ c.realize := by
  classical
  let : binaryRelLanguage.Structure M := binaryRelStructure M (fun a b => a < b)
  have hlist (l : List (Cell M)) :
      ∃ ψ : binaryRelLanguage.BoundedFormula M 1, ψ.IsQF ∧
        ∀ x : M, ψ.Realize id ![x] ↔ ∃ c ∈ l, x ∈ c.realize := by
    induction l with
    | nil => exact ⟨⊥, BoundedFormula.isQF_bot, fun x => by simp⟩
    | cons c l ih =>
      obtain ⟨ψ, hψ, h⟩ := ih
      refine ⟨c.toBoundedFormula ⊔ ψ, c.toBoundedFormula_isQF.sup hψ, ?_⟩
      intro x
      simp only [BoundedFormula.realize_sup, c.toBoundedFormula_realize x, h x,
        List.mem_cons, exists_eq_or_imp]
  obtain ⟨ψ, hψ, h⟩ := hlist s.toList
  exact ⟨ψ, hψ, fun x => by simpa only [Finset.mem_toList] using h x⟩

theorem equality_parameterfree_unary {M : Type u} [Infinite M]
    (φ : Formula false 1) (x y : M) :
    φ.Realize noRelation ![x] ↔ φ.Realize noRelation ![y] := by
  apply realize_of_patterns equality_extends equality_extends
  rintro (⟨i, j⟩ | ⟨r, _, _⟩)
  · have hi : i = 0 := Subsingleton.elim _ _
    have hj : j = 0 := Subsingleton.elim _ _
    subst i; subst j
    simp [realizeAtom]
  · exact isEmptyElim r

theorem dlo_parameterfree_unary {M : Type u} [LinearOrder M] [DenselyOrdered M]
    [NoMinOrder M] [NoMaxOrder M] [Nonempty M]
    (φ : Formula true 1) (x y : M) :
    φ.Realize (fun a b : M => a < b) ![x] ↔ φ.Realize (fun a b : M => a < b) ![y] := by
  apply realize_of_patterns dlo_extends dlo_extends
  rintro (⟨i, j⟩ | ⟨_, i, j⟩)
  · have hi : i = 0 := Subsingleton.elim _ _
    have hj : j = 0 := Subsingleton.elim _ _
    subst i; subst j
    simp [realizeAtom]
  · have hi : i = 0 := Subsingleton.elim _ _
    have hj : j = 0 := Subsingleton.elim _ _
    subst i; subst j
    simp [realizeAtom]

/-- The semantic clauses of the six strict-order axioms displayed in the entry. -/
structure DloAxioms {M : Type u} (r : M → M → Prop) : Prop where
  irrefl : ∀ a, ¬r a a
  trans : ∀ a b c, r a b → r b c → r a c
  total : ∀ a b, r a b ∨ a = b ∨ r b a
  dense : ∀ a b, r a b → ∃ c, r a c ∧ r c b
  noMin : ∀ a, ∃ b, r b a
  noMax : ∀ a, ∃ b, r a b

theorem dlo_axioms_of_order {M : Type u} [LinearOrder M] [DenselyOrdered M]
    [NoMinOrder M] [NoMaxOrder M] :
    DloAxioms (fun a b : M => a < b) :=
  ⟨fun a => lt_irrefl a, fun _ _ _ => lt_trans, lt_trichotomy,
    fun _ _ => exists_between, exists_lt, exists_gt⟩

/-- The strict axioms suffice; an arbitrary relation satisfying them can be
equipped with the corresponding linear order without changing its interpretation. -/
theorem dlo_axioms_quantifier_elimination {M : Type u} [Nonempty M]
    (r : M → M → Prop) (h : DloAxioms r) {n} (φ : Formula true n) (x : Fin n → M) :
    (dloEliminate φ).IsQF ∧
      ((dloEliminate φ).Realize r x ↔ φ.Realize r x) := by
  classical
  let : IsStrictTotalOrder M r :=
    { irrefl := h.irrefl, trans := h.trans, trichotomous := fun a b hab hba => ((h.total a b).resolve_left hab).resolve_right hba }
  let : LinearOrder M := linearOrderOfSTO r
  let : DenselyOrdered M := ⟨h.dense⟩
  let : NoMinOrder M := ⟨h.noMin⟩
  let : NoMaxOrder M := ⟨h.noMax⟩
  exact ⟨(dlo_quantifier_elimination.{u} φ).1, (dlo_quantifier_elimination φ).2 M x⟩

end Lemmatheca.ModelTheory.QuantifierElimination
