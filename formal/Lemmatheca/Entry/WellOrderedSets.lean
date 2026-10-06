import Lemmatheca.SetTheory.Basic
import Lemmatheca.SetTheory.WellOrders

/-! Particular examples and counterexamples for the human entry. -/

namespace Lemmatheca.Entry.WellOrderedSets
open Lemmatheca.SetTheory

open Lemmatheca.SetTheory

theorem usual_orders_fail :
    ¬ WellFounded ((· < ·) : ℤ → ℤ → Prop) ∧
    ¬ WellFounded ((· < ·) : ℚ → ℚ → Prop) ∧
    ¬ WellFounded ((· < ·) : ℝ → ℝ → Prop) ∧
    ¬ WellFounded ((· < ·) : Set.Icc (0 : ℝ) 1 → Set.Icc (0 : ℝ) 1 → Prop) ∧
    (∀ z : ℤ, z - 1 < z) ∧
    (∀ x : ℚ, x ∈ Set.Ioo 0 1 → x / 2 ∈ Set.Ioo 0 1 ∧ x / 2 < x) ∧
    (∀ x : ℝ, x ∈ Set.Ioo 0 1 → x / 2 ∈ Set.Ioo 0 1 ∧ x / 2 < x) := by
  refine ⟨noMin_not_wellFounded ℤ, noMin_not_wellFounded ℚ, noMin_not_wellFounded ℝ,
    ?_, (fun z => by omega), ?_, ?_⟩
  · intro h
    let s : Set (Set.Icc (0 : ℝ) 1) := {x | 0 < x.val}
    have hs : s.Nonempty := ⟨⟨1, by norm_num⟩, by norm_num [s]⟩
    obtain ⟨a, ha, hmin⟩ := h.has_min s hs
    change 0 < a.val at ha
    let b : Set.Icc (0 : ℝ) 1 := ⟨a.val / 2, by
      have := a.property
      constructor <;> linarith [a.property.1, a.property.2]⟩
    have hb : b ∈ s := by change 0 < a.val / 2; exact div_pos ha (by norm_num)
    exact hmin b hb (by change a.val / 2 < a.val; linarith)
  · intro x hx
    constructor
    · constructor <;> linarith [hx.1, hx.2]
    · linarith [hx.1]
  · intro x hx
    constructor
    · constructor <;> linarith [hx.1, hx.2]
    · linarith [hx.1]

theorem discrete_two_has_no_least :
    ¬ Std.Total ((· = ·) : Fin 2 → Fin 2 → Prop) ∧
    ¬ ∃ a : Fin 2, ∀ b : Fin 2, a = b := by
  constructor
  · intro h
    have := h.total (0 : Fin 2) 1
    norm_num at this
  · rintro ⟨a, ha⟩
    have h := (ha 0).symm.trans (ha 1)
    norm_num at h

def topEnumeration : ℕ → WithTop ℕ
  | 0 => ⊤
  | n + 1 => (n : WithTop ℕ)

theorem topEnumeration_bijective : Function.Bijective topEnumeration := by
  constructor
  · intro a b h
    cases a with
    | zero =>
      cases b with
      | zero => rfl
      | succ b => cases h
    | succ a =>
      cases b with
      | zero => cases h
      | succ b => exact congrArg Nat.succ (Option.some.inj h)
  · intro x
    cases x with
    | top => exact ⟨0, rfl⟩
    | coe n => exact ⟨n + 1, rfl⟩

theorem top_order_structure :
    Set.Iio (⊤ : WithTop ℕ) = Set.range (fun n : ℕ => (n : WithTop ℕ)) ∧
    Order.IsSuccLimit (⊤ : WithTop ℕ) ∧ IsMax (⊤ : WithTop ℕ) ∧
    (∀ n : ℕ, (n : WithTop ℕ) ⋖ ((n + 1 : ℕ) : WithTop ℕ)) ∧
    ¬ Nonempty (WithTop ℕ ≃o ℕ) := by
  refine ⟨?_, WithTop.isSuccLimit_top, isMax_top, ?_, ?_⟩
  · ext x
    cases x <;> simp
  · intro n
    exact WithTop.coe_covBy_coe.mpr (show n ⋖ n + 1 from ⟨by omega, by intro c h1 h2; omega⟩)
  · rintro ⟨e⟩
    have h := e.monotone (le_top : e.symm (e ⊤ + 1) ≤ ⊤)
    simp only [e.apply_symm_apply] at h
    omega

theorem lex_predecessors :
    Set.Iio (toLex (1, 0) : ℕ ×ₗ ℕ) =
      Set.range (fun n : ℕ => (toLex (0, n) : ℕ ×ₗ ℕ)) ∧
    (Set.Iio (toLex (1, 0) : ℕ ×ₗ ℕ)).Infinite ∧
    ¬ Nonempty ((ℕ ×ₗ ℕ) ≃o ℕ) := by
  have heq : Set.Iio (toLex (1, 0) : ℕ ×ₗ ℕ) =
      Set.range (fun n : ℕ => (toLex (0, n) : ℕ ×ₗ ℕ)) := by
    ext x
    rcases x with ⟨i, j⟩
    change (toLex (i, j) : ℕ ×ₗ ℕ) < toLex (1, 0) ↔
      ∃ n : ℕ, (toLex (0, n) : ℕ ×ₗ ℕ) = toLex (i, j)
    simp only [Prod.Lex.toLex_lt_toLex, toLex_inj, Prod.mk.injEq]
    constructor
    · intro h
      exact ⟨j, by omega, rfl⟩
    · rintro ⟨n, rfl, rfl⟩
      exact Or.inl (by omega)
  have hinf : (Set.Iio (toLex (1, 0) : ℕ ×ₗ ℕ)).Infinite := by
    rw [heq]
    exact Set.infinite_range_of_injective (fun a b h => by simpa using h)
  refine ⟨heq, hinf, ?_⟩
  rintro ⟨e⟩
  have hfin := (Set.finite_Iio (e (toLex (1, 0)))).preimage e.injective.injOn
  apply hinf
  convert hfin using 1
  ext x
  simp

theorem lex_successors_limits :
    (∀ i j : ℕ, (toLex (i, j) : ℕ ×ₗ ℕ) ⋖ (toLex (i, j + 1) : ℕ ×ₗ ℕ)) ∧
    ∀ i : ℕ, 0 < i → Order.IsSuccLimit (toLex (i, 0) : ℕ ×ₗ ℕ) := by
  constructor
  · intro i j
    exact Prod.Lex.toLex_covBy_toLex_iff.mpr (Or.inl ⟨rfl, (show j ⋖ j + 1 from ⟨by omega, by intro c h1 h2; omega⟩)⟩)
  · intro i hi
    refine ⟨?_, ?_⟩
    · rw [isMin_iff_forall_not_lt]
      intro h
      exact h (toLex (0, 0)) (Prod.Lex.toLex_lt_toLex.mpr (Or.inl hi))
    · intro a ha
      rcases a with ⟨k, m⟩
      rcases Prod.Lex.toLex_covBy_toLex_iff.mp ha with ⟨_, h⟩ | ⟨_, hm, _⟩
      · exact (not_lt_of_ge (Nat.zero_le m)) h.lt
      · exact (not_isMax m) hm

theorem proper_subsets_not_initial :
    ¬ IsLowerSet Lemmatheca.SetTheory.evenNaturals ∧
    ¬ IsLowerSet {n : ℕ | 0 < n} := by
  constructor
  · intro h
    have h2 : 2 ∈ Lemmatheca.SetTheory.evenNaturals := by
      exact ⟨1, rfl⟩
    obtain ⟨k, hk⟩ := h (show (1 : ℕ) ≤ 2 by decide) h2
    omega
  · intro h
    exact Nat.not_lt_zero 0 (h (show (0 : ℕ) ≤ 1 by decide)
      (show 1 ∈ {n : ℕ | 0 < n} from Nat.zero_lt_succ 0))

theorem missing_limit_case :
    (0 : WithTop ℕ) ≠ ⊤ ∧
    (∀ a b : WithTop ℕ, a ⋖ b → a ≠ ⊤ → b ≠ ⊤) ∧
    (∀ x : WithTop ℕ, x < ⊤ → x ≠ ⊤) ∧
    ¬ ((⊤ : WithTop ℕ) ≠ ⊤) := by
  refine ⟨WithTop.coe_ne_top, ?_, (fun x hx => ne_of_lt hx), by simp⟩
  intro a b hab _ hb
  subst b
  exact WithTop.isSuccLimit_top.isSuccPrelimit a hab

/-- p = 0, q = 1, r = 2; only p R r and q R r hold. -/
def forkDependency (a b : Fin 3) : Prop := (a = 0 ∨ a = 1) ∧ b = 2

theorem forkDependency_spec :
    WellFounded forkDependency ∧
    ¬ forkDependency 0 1 ∧ ¬ forkDependency 1 0 ∧
    (∀ b ∈ ({2} : Set (Fin 3)), ¬ forkDependency b 2) := by
  refine ⟨(measure (fun a : Fin 3 => a.val)).wf.mono ?_, ?_, ?_, ?_⟩
  · intro a b h
    change a.val < b.val
    rcases h with ⟨rfl | rfl, rfl⟩ <;> decide
  · norm_num [forkDependency]
  · norm_num [forkDependency]
  · intro b hb
    simp only [Set.mem_singleton_iff] at hb
    subst b
    norm_num [forkDependency]

theorem factorial_prefix : (List.range 5).map Nat.factorial = [1, 1, 2, 6, 24] := by
  decide

def limitSetValue : WithTop ℕ → Set ℕ
  | none => Set.univ
  | some n => Set.Iio n

/-- Rules are defined even for histories that are not solutions. -/
def limitSetRule : RecursionRule (WithTop ℕ) (Set ℕ)
  | none, h => ⋃ n : ℕ, h ⟨(n : WithTop ℕ), WithTop.coe_lt_top n⟩
  | some 0, _ => ∅
  | some (n + 1), h => h ⟨(n : WithTop ℕ), by
      change (n : WithTop ℕ) < ((n + 1 : ℕ) : WithTop ℕ)
      exact WithTop.coe_lt_coe.mpr (Nat.lt_succ_self n)⟩ ∪ {n}

theorem limitSetValue_spec :
    (∀ x, limitSetValue x = limitSetRule x (fun b => limitSetValue b.val)) ∧
    limitSetValue 0 = ∅ ∧
    (∀ n : ℕ, limitSetValue ((n + 1 : ℕ) : WithTop ℕ) =
      limitSetValue (n : WithTop ℕ) ∪ {n}) ∧
    limitSetValue ⊤ = ⋃ n : ℕ, limitSetValue (n : WithTop ℕ) ∧
    limitSetValue ⊤ = Set.univ := by
  refine ⟨?_, ?_, ?_, ?_, rfl⟩
  · intro x
    cases x with
    | top => exact natural_segment_union.symm
    | coe n =>
      cases n with
      | zero => ext k; simp [limitSetValue, limitSetRule]
      | succ n => exact natural_segment_step n
  · ext k; simp [limitSetValue]
  · exact natural_segment_step
  · exact natural_segment_union.symm

theorem successor_rules_leave_top_free (s : Set ℕ) :
    ∃ F : WithTop ℕ → Set ℕ, F 0 = ∅ ∧
      (∀ n : ℕ, F ((n + 1 : ℕ) : WithTop ℕ) = F (n : WithTop ℕ) ∪ {n}) ∧ F ⊤ = s := by
  refine ⟨(fun x => match x with | none => s | some n => Set.Iio n), ?_, ?_, rfl⟩
  · ext k; simp
  · exact natural_segment_step

end Lemmatheca.Entry.WellOrderedSets
