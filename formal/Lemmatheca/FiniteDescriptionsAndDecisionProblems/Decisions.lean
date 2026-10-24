import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Vector
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.NormNum

/-! Numerical decision problems and the model-independent diagonal obstruction. -/

namespace Lemmatheca.ComputabilityTheory.PrimitiveRecursion

noncomputable def characteristic {α : Type*} (R : α → Prop) (x : α) : ℕ := by
  classical
  exact if R x then 1 else 0

theorem characteristic_spec {α : Type*} (R : α → Prop) (x : α) :
    (characteristic R x = 1 ↔ R x) ∧ (characteristic R x = 0 ↔ ¬ R x) := by
  classical
  by_cases h : R x <;> simp [characteristic, h]

end Lemmatheca.ComputabilityTheory.PrimitiveRecursion

namespace Lemmatheca.ComputabilityTheory.FiniteDescriptions

open PrimitiveRecursion

/-- The repeated-subtraction procedure records its number of subtractions and final remainder. -/
def parityTrace (n : ℕ) : ℕ × ℕ :=
  if n < 2 then (0, n)
  else let trace := parityTrace (n - 2); (trace.1 + 1, trace.2)
termination_by n
decreasing_by omega

def parityTest (n : ℕ) : ℕ := if (parityTrace n).2 = 0 then 1 else 0

theorem characteristic_values (A : Set ℕ) (n : ℕ) :
    characteristic A n = 0 ∨ characteristic A n = 1 := by
  classical
  unfold characteristic
  split <;> simp

theorem characteristic_injective :
    Function.Injective (fun A : Set ℕ => characteristic A) := by
  intro A B h
  ext n
  change characteristic (fun n => n ∈ A) = characteristic (fun n => n ∈ B) at h
  have hn := congrFun h n
  rw [← (characteristic_spec (fun n => n ∈ A) n).1,
    ← (characteristic_spec (fun n => n ∈ B) n).1, hn]

theorem binary_function_characteristic (f : ℕ → ℕ)
    (hf : ∀ n, f n = 0 ∨ f n = 1) :
    ∃! A : Set ℕ, characteristic A = f := by
  classical
  have h : characteristic {n | f n = 1} = f := by
    funext n
    rcases hf n with hn | hn <;> simp [characteristic, Set.ofPred, hn]
  refine ⟨{n | f n = 1}, h, ?_⟩
  intro B hB
  exact characteristic_injective (hB.trans h.symm)

theorem parityTrace_spec (n : ℕ) :
    n = 2 * (parityTrace n).1 + (parityTrace n).2 ∧
      (parityTrace n).2 < 2 ∧ (parityTrace n).1 ≤ n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n < 2
    · have ht : parityTrace n = (0, n) := by rw [parityTrace]; simp [hn]
      simp only [ht]
      omega
    · have hlt : n - 2 < n := by omega
      obtain ⟨heq, hr, hj⟩ := ih (n - 2) hlt
      have ht : parityTrace n = ((parityTrace (n - 2)).1 + 1,
          (parityTrace (n - 2)).2) := by rw [parityTrace]; simp [hn]
      simp only [ht]
      omega

theorem parityTest_correct (n : ℕ) :
    parityTest n = characteristic (fun n => ∃ k, n = 2 * k) n := by
  classical
  obtain ⟨heq, hr, _⟩ := parityTrace_spec n
  have heven : (∃ k, n = 2 * k) ↔ (parityTrace n).2 = 0 := by
    constructor
    · rintro ⟨k, hk⟩
      omega
    · intro hzero
      exact ⟨(parityTrace n).1, by omega⟩
  simp only [parityTest, characteristic, heven]

/-- The scan records the answer and the number of equality comparisons made. -/
def lookupTrace : List ℕ → ℕ → ℕ × ℕ
  | [], _ => (0, 0)
  | a :: tail, n => if n = a then (1, 1)
      else let trace := lookupTrace tail n; (trace.1, trace.2 + 1)

theorem lookupTrace_spec (L : List ℕ) (n : ℕ) :
    (lookupTrace L n).1 = characteristic (fun n => n ∈ L) n ∧
      (lookupTrace L n).2 ≤ L.length := by
  classical
  induction L with
  | nil => simp [lookupTrace, characteristic]
  | cons a L ih =>
    by_cases h : n = a
    · simp [lookupTrace, h, characteristic]
    · constructor
      · by_cases hm : n ∈ L <;> simpa [lookupTrace, h, characteristic, hm] using ih.1
      · simpa [lookupTrace, h] using Nat.add_le_add_right ih.2 1

theorem finite_set_list (A : Set ℕ) (hA : A.Finite) :
    ∃ L : List ℕ, ∀ n, n ∈ L ↔ n ∈ A := by
  classical
  exact ⟨hA.toFinset.toList, by simp⟩

theorem bounded_table_counterexample (B : ℕ) :
    (∅ : Set ℕ) ≠ {B} ∧
      (∀ n < B, characteristic (∅ : Set ℕ) n = characteristic ({B} : Set ℕ) n) ∧
      characteristic (∅ : Set ℕ) B = 0 ∧ characteristic ({B} : Set ℕ) B = 1 := by
  classical
  change (∅ : Set ℕ) ≠ {B} ∧
    (∀ n < B, characteristic (fun n => n ∈ (∅ : Set ℕ)) n =
      characteristic (fun n => n ∈ ({B} : Set ℕ)) n) ∧
    characteristic (fun n => n ∈ (∅ : Set ℕ)) B = 0 ∧
    characteristic (fun n => n ∈ ({B} : Set ℕ)) B = 1
  refine ⟨by simp, ?_, by simp [characteristic], by simp [characteristic]⟩
  intro n hn
  simp [characteristic, Nat.ne_of_lt hn]

/-- False represents digit zero, and true represents digit one. -/
def wordCode : List Bool → ℕ
  | [] => 0
  | b :: w => 2 * wordCode w + b.toNat + 1

theorem wordCode_injective : Function.Injective wordCode := by
  intro u
  induction u with
  | nil =>
    intro v h
    cases v with
    | nil => rfl
    | cons d v => simp only [wordCode] at h; omega
  | cons b u ih =>
    intro v h
    cases v with
    | nil => simp only [wordCode] at h; omega
    | cons d v =>
      have hb : b = d := by
        cases b <;> cases d <;> simp only [wordCode, Bool.toNat_false, Bool.toNat_true] at h <;> first | rfl | omega
      have ht : wordCode u = wordCode v := by
        simp only [wordCode, hb] at h
        omega
      exact congrArg₂ List.cons hb (ih ht)

theorem wordCode_subtype_injective (P : List Bool → Prop) :
    Function.Injective (fun w : {w : List Bool // P w} => wordCode w.val) := by
  intro u v h
  exact Subtype.ext (wordCode_injective h)

theorem wordCode_head_tail (b : Bool) (w : List Bool) :
    (wordCode (b :: w) - 1) % 2 = b.toNat ∧
      (wordCode (b :: w) - 1) / 2 = wordCode w := by
  cases b <;> simp only [wordCode, Bool.toNat_false, Bool.toNat_true] <;> omega

theorem fixed_word_count (k : ℕ) : Fintype.card (List.Vector Bool k) = 2 ^ k := by
  rw [Fintype.card_congr (Equiv.vectorEquivFin Bool k)]
  simp

theorem fixed_blocks_exist {α : Type*} [Fintype α] (k : ℕ)
    (hcard : Fintype.card α ≤ 2 ^ k) :
    ∃ b : α → List Bool, Function.Injective b ∧ ∀ a, (b a).length = k := by
  classical
  have hc : Fintype.card α ≤ Fintype.card (List.Vector Bool k) := by
    simpa only [fixed_word_count] using hcard
  obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le hc
  refine ⟨fun a => (f a).toList, ?_, ?_⟩
  · intro a d h
    exact f.injective (Subtype.ext h)
  · intro a
    exact (f a).property

theorem alphabet_bound (q : ℕ) : q ≤ 2 ^ (q + 1) := by
  induction q with
  | zero => simp
  | succ q ih =>
    have hp : 0 < 2 ^ (q + 1) := pow_pos (by decide) _
    rw [pow_succ]
    omega

theorem fixed_block_code_injective {α : Type*} (b : α → List Bool) (k : ℕ)
    (hk : 0 < k) (hinj : Function.Injective b) (hlen : ∀ a, (b a).length = k) :
    Function.Injective (fun w : List α => wordCode (w.flatMap b)) := by
  have hflat : Function.Injective (List.flatMap b) := by
    intro u
    induction u with
    | nil =>
      intro v h
      cases v with
      | nil => rfl
      | cons d v =>
        have hl := congrArg List.length h
        simp only [List.flatMap_nil, List.flatMap_cons, List.length_nil,
          List.length_append, hlen] at hl
        omega
    | cons a u ih =>
      intro v h
      cases v with
      | nil =>
        have hl := congrArg List.length h
        simp only [List.flatMap_nil, List.flatMap_cons, List.length_nil,
          List.length_append, hlen] at hl
        omega
      | cons d v =>
        change b a ++ u.flatMap b = b d ++ v.flatMap b at h
        have hl : (b a).length = (b d).length := (hlen a).trans (hlen d).symm
        have hb := List.append_inj_left h hl
        have ht := List.append_inj_right h hl
        exact congrArg₂ List.cons (hinj hb) (ih ht)
  exact wordCode_injective.comp hflat

/-- A family has at most one numerical output at each program-input pair. -/
abbrev BehaviorFamily := ℕ → ℕ → Option ℕ

/-- Functionality of a relation expressing outputs. -/
def FunctionalOutputs (R : ℕ → ℕ → ℕ → Prop) : Prop :=
  ∀ e x a b, R e x a → R e x b → a = b

/-- A classical conversion of unique-output relations to optional values. -/
noncomputable def familyFromGraph (R : ℕ → ℕ → ℕ → Prop) : BehaviorFamily := by
  classical
  exact fun e x => if h : ∃ y, R e x y then some (Classical.choose h) else none

theorem familyFromGraph_spec (R : ℕ → ℕ → ℕ → Prop) (hR : FunctionalOutputs R)
    (e x y : ℕ) : familyFromGraph R e x = some y ↔ R e x y := by
  classical
  by_cases h : ∃ z, R e x z
  · simp only [familyFromGraph, dite_eq_left h]
    constructor
    · intro hy
      have heq := Option.some.inj hy
      exact heq ▸ Classical.choose_spec h
    · intro hy
      exact congrArg some (hR e x _ _ (Classical.choose_spec h) hy)
  · simp only [familyFromGraph, dite_eq_right h]
    constructor
    · intro hy
      cases hy
    · intro hy
      exact False.elim (h ⟨y, hy⟩)

/-- Numbering any collection of programs extends its semantics to all natural indices. -/
noncomputable def extendPrograms {P : Type*} (code : P → ℕ)
    (eval : P → ℕ → Option ℕ) : BehaviorFamily := by
  classical
  exact fun e x => if h : ∃ p, code p = e then eval (Classical.choose h) x else none

theorem extendPrograms_agrees {P : Type*} (code : P → ℕ)
    (hinj : Function.Injective code) (eval : P → ℕ → Option ℕ) (p : P) (x : ℕ) :
    extendPrograms code eval (code p) x = eval p x := by
  classical
  have h : ∃ q, code q = code p := ⟨p, rfl⟩
  have hp : Classical.choose h = p := hinj (Classical.choose_spec h)
  simp only [extendPrograms, dite_eq_left h, hp]

theorem extendPrograms_unused {P : Type*} (code : P → ℕ)
    (eval : P → ℕ → Option ℕ) (e x : ℕ) (h : ¬ ∃ p, code p = e) :
    extendPrograms code eval e x = none := by
  classical
  simp only [extendPrograms, dite_eq_right h]

/-- An index decides a set when every output exists and is its correct binary answer. -/
def Decides (E : BehaviorFamily) (e : ℕ) (A : Set ℕ) : Prop :=
  ∀ x, E e x = some (characteristic A x)

def DecidableRelative (E : BehaviorFamily) (A : Set ℕ) : Prop := ∃ e, Decides E e A

theorem decides_outputs (E : BehaviorFamily) (e : ℕ) (A : Set ℕ)
    (h : Decides E e A) :
    (∀ x, ∃ y, E e x = some y) ∧
      (∀ x, E e x = some 0 ∨ E e x = some 1) ∧
      (∀ x, E e x = some 1 ↔ x ∈ A) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x
    exact ⟨characteristic A x, h x⟩
  · intro x
    rcases characteristic_values A x with hx | hx
    · exact Or.inl ((h x).trans (congrArg some hx))
    · exact Or.inr ((h x).trans (congrArg some hx))
  · intro x
    rw [h x, Option.some.injEq]
    exact (characteristic_spec A x).1

theorem every_problem_has_interpretation (A : Set ℕ) :
    Decides (fun _ x => some (characteristic A x)) 0 A := by
  intro x
  rfl

def diagonalProblem (E : BehaviorFamily) : Set ℕ := {e | E e e ≠ some 1}

theorem diagonal_membership (E : BehaviorFamily) (e : ℕ) :
    e ∈ diagonalProblem E ↔ E e e = none ∨ ∃ y, E e e = some y ∧ y ≠ 1 := by
  change E e e ≠ some 1 ↔ E e e = none ∨ ∃ y, E e e = some y ∧ y ≠ 1
  cases h : E e e <;> simp

theorem diagonal_no_decider (E : BehaviorFamily) (e : ℕ) :
    ¬ Decides E e (diagonalProblem E) := by
  intro h
  have hx := h e
  by_cases he : E e e = some 1
  · have hm : e ∉ diagonalProblem E := by
      simpa only [diagonalProblem, Set.mem_ofPred_eq, not_not] using he
    have hc := (characteristic_spec (diagonalProblem E) e).2.mpr hm
    rw [hc, he] at hx
    cases hx
  · have hm : e ∈ diagonalProblem E := he
    have hc := (characteristic_spec (diagonalProblem E) e).1.mpr hm
    exact he (hx.trans (congrArg some hc))

theorem exists_undecidable (E : BehaviorFamily) :
    ∃ A : Set ℕ, ¬ DecidableRelative E A := by
  refine ⟨diagonalProblem E, ?_⟩
  rintro ⟨e, he⟩
  exact diagonal_no_decider E e he

end Lemmatheca.ComputabilityTheory.FiniteDescriptions
