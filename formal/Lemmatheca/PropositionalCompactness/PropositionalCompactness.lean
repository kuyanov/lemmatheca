import Lemmatheca.PropositionalProofs.Deduction
import Lemmatheca.FiniteConstraintsAndDistinctRepresentatives.RadoHall
import Mathlib.Order.KonigLemma
import Mathlib.SetTheory.Cardinal.Finite

/-! Set-premise propositional semantics and compactness for the shared syntax.
Finite proof contexts keep the exact classical natural-deduction calculus.
The prefix-tree construction specializes the atom type to natural numbers;
its compatible finite levels give the countable-atom argument. -/

namespace Lemmatheca.MathematicalLogic.PropositionalCompactness

open Lemmatheca.MathematicalLogic.Propositional

universe u
variable {α : Type u} [DecidableEq α]

abbrev Theory (α : Type u) := Set (PropFormula α)

def ModelsTheory (v : Valuation α) (Γ : Theory α) : Prop :=
  ∀ A ∈ Γ, Satisfies v A

def TheorySatisfiable (Γ : Theory α) : Prop :=
  ∃ v, ModelsTheory v Γ

def FiniteSatisfiable (Γ : Theory α) : Prop :=
  ∀ Δ : Finset (PropFormula α), (↑Δ : Set (PropFormula α)) ⊆ Γ → Satisfiable Δ

def TheoryEntails (Γ : Theory α) (C : PropFormula α) : Prop :=
  ∀ v, ModelsTheory v Γ → Satisfies v C

/-- All finite-domain rows satisfying every premise supported on that domain. -/
def AllowedRows (Γ : Theory α) (F : Finset α) : Set (F → Bool) :=
  {r | ∀ A ∈ Γ, atoms A ⊆ F → Satisfies (extendRow F r) A}

theorem finite_atom_stock (F : Finset α) (Γ : Theory α)
    (hfin : FiniteSatisfiable Γ) (hsupport : ∀ A ∈ Γ, atoms A ⊆ F) :
    ∃ r : F → Bool, ModelsTheory (extendRow F r) Γ := by
  classical
  by_contra hn
  simp only [ModelsTheory, not_exists, not_forall] at hn
  choose A hA hfalse using hn
  let Δ : Finset (PropFormula α) := Finset.univ.image A
  have hΔ : (↑Δ : Set (PropFormula α)) ⊆ Γ := by
    intro B hB
    obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hB
    exact hA r
  obtain ⟨v, hv⟩ := hfin Δ hΔ
  let r : F → Bool := fun a => v a
  apply hfalse r
  have hval := hv (A r) (Finset.mem_image.mpr ⟨r, Finset.mem_univ _, rfl⟩)
  change eval (extendRow F r) (A r) = true
  rw [eval_congr (A r) (extendRow F r) v (fun a ha => by
    simp [extendRow, r, hsupport (A r) (hA r) ha])]
  exact hval

theorem allowed_rows_nonempty (Γ : Theory α) (hfin : FiniteSatisfiable Γ)
    (F : Finset α) : (AllowedRows Γ F).Nonempty := by
  let Δ : Theory α := {A | A ∈ Γ ∧ atoms A ⊆ F}
  have hΔ : FiniteSatisfiable Δ := by
    intro B hB
    exact hfin B (fun A hA => (hB hA).1)
  obtain ⟨r, hr⟩ := finite_atom_stock F Δ hΔ (fun A hA => hA.2)
  exact ⟨r, fun A hA hF => hr A ⟨hA, hF⟩⟩

theorem allowed_rows_restrict (Γ : Theory α) (F G : Finset α) (hFG : F ⊆ G)
    (r : G → Bool) (hr : r ∈ AllowedRows Γ G) :
    (fun i : F => r (Set.inclusion hFG i)) ∈ AllowedRows Γ F := by
  intro A hA hF
  have he : eval (extendRow F (fun i => r (Set.inclusion hFG i))) A =
      eval (extendRow G r) A := by
    apply eval_congr
    intro a ha
    have hf := hF ha
    simp [extendRow, hf, hFG hf]
  change eval _ A = true
  rw [he]
  exact hr A hA (hF.trans hFG)

/-- A length-n binary word, extended by zero after its last assigned atom. -/
def prefixValuation {n : ℕ} (r : Fin n → Bool) : Valuation ℕ :=
  fun k => if h : k < n then r ⟨k, h⟩ else false

/-- Retained words never falsify a premise whose entire support is assigned. -/
def PrefixSurvives (Γ : Theory ℕ) (n : ℕ) (r : Fin n → Bool) : Prop :=
  ∀ A ∈ Γ, atoms A ⊆ Finset.range n → Satisfies (prefixValuation r) A

theorem prefix_level_nonempty (Γ : Theory ℕ) (hfin : FiniteSatisfiable Γ) (n : ℕ) :
    ∃ r : Fin n → Bool, PrefixSurvives Γ n r := by
  obtain ⟨r, hr⟩ := allowed_rows_nonempty Γ hfin (Finset.range n)
  let s : Fin n → Bool := fun i => r ⟨i, Finset.mem_range.mpr i.isLt⟩
  refine ⟨s, fun A hA hF => ?_⟩
  have he : eval (prefixValuation s) A = eval (extendRow (Finset.range n) r) A := by
    apply eval_congr
    intro a ha
    have hn : a < n := Finset.mem_range.mp (hF ha)
    simp [prefixValuation, extendRow, s, hn]
  change eval _ A = true
  rw [he]
  exact hr A hA hF

theorem prefix_level_bound (Γ : Theory ℕ) (n : ℕ) :
    Nat.card {r : Fin n → Bool // PrefixSurvives Γ n r} ≤ 2 ^ n := by
  have h := Nat.card_le_card_of_injective
    (fun r : {r : Fin n → Bool // PrefixSurvives Γ n r} => r.1) Subtype.val_injective
  simpa [Nat.card_eq_fintype_card, Fintype.card_fun] using h

theorem prefix_survives_restrict (Γ : Theory ℕ) {m n : ℕ} (hmn : m ≤ n)
    (r : Fin n → Bool) (hr : PrefixSurvives Γ n r) :
    PrefixSurvives Γ m (fun i => r (Fin.castLE hmn i)) := by
  intro A hA hF
  have hG : atoms A ⊆ Finset.range n := hF.trans (Finset.range_mono hmn)
  have he : eval (prefixValuation (fun i => r (Fin.castLE hmn i))) A =
      eval (prefixValuation r) A := by
    apply eval_congr
    intro a ha
    have ham : a < m := Finset.mem_range.mp (hF ha)
    have han : a < n := ham.trans_le hmn
    simp [prefixValuation, ham, han]
  change eval _ A = true
  rw [he]
  exact hr A hA hG

/-- An infinite path whose restriction belongs to every retained level. -/
theorem prefix_branch_exists (Γ : Theory ℕ) (hfin : FiniteSatisfiable Γ) :
    ∃ v : Valuation ℕ, ∀ n, PrefixSurvives Γ n (fun i => v i) := by
  classical
  let T (n : ℕ) := {r : Fin n → Bool // PrefixSurvives Γ n r}
  have hnonempty (n : ℕ) : Nonempty (T n) := by
    obtain ⟨r, hr⟩ := prefix_level_nonempty Γ hfin n
    exact ⟨⟨r, hr⟩⟩
  let (n : ℕ) : Nonempty (T n) := hnonempty n
  let π : {i j : ℕ} → (hij : i ≤ j) → T j → T i :=
    fun {i j} hij r => ⟨fun k => r.1 (Fin.castLE hij k),
      prefix_survives_restrict Γ hij r.1 r.2⟩
  have hrefl {i : ℕ} (r : T i) : π le_rfl r = r := by
    apply Subtype.ext
    funext k
    rfl
  have htrans {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) (r : T k) :
      π hij (π hjk r) = π (hij.trans hjk) r := by
    apply Subtype.ext
    funext a
    rfl
  obtain ⟨f, hf⟩ := exists_seq_forall_proj_of_forall_finite π (fun {i} r => hrefl r)
    (fun {i j k} hij hjk r => htrans hij hjk r) (fun i r => Set.toFinite _)
  let v : Valuation ℕ := fun k => (f (k + 1)).1 ⟨k, Nat.lt_succ_self k⟩
  refine ⟨v, fun n => ?_⟩
  have hrow : (fun i : Fin n => v i) = (f n).1 := by
    funext i
    have hi : i.val + 1 ≤ n := Nat.succ_le_of_lt i.isLt
    have he := congrArg (fun r : T (i.val + 1) => r.1 ⟨i, Nat.lt_succ_self i⟩) (hf hi)
    exact he.symm
  rw [hrow]
  exact (f n).2

theorem prefix_branch_models (Γ : Theory ℕ) (v : Valuation ℕ)
    (hv : ∀ n, PrefixSurvives Γ n (fun i => v i)) : ModelsTheory v Γ := by
  intro A hA
  obtain ⟨n, hn⟩ := Finset.exists_nat_subset_range (atoms A)
  have h := hv n A hA hn
  have he : eval (prefixValuation (fun i : Fin n => v i)) A = eval v A := by
    apply eval_congr
    intro a ha
    simp [prefixValuation, Finset.mem_range.mp (hn ha)]
  change eval v A = true
  rw [← he]
  exact h

theorem countable_compactness (Γ : Theory ℕ) (hfin : FiniteSatisfiable Γ) :
    TheorySatisfiable Γ := by
  obtain ⟨v, hv⟩ := prefix_branch_exists Γ hfin
  exact ⟨v, prefix_branch_models Γ v hv⟩

theorem compactness (Γ : Theory α) :
    TheorySatisfiable Γ ↔ FiniteSatisfiable Γ := by
  constructor
  · rintro ⟨v, hv⟩ Δ hΔ
    exact ⟨v, fun A hA => hv A (hΔ hA)⟩
  · intro hfin
    obtain ⟨v, hv⟩ := Lemmatheca.SetTheory.RadoHall.finite_constraint_solution
      (β := fun _ : α => Bool) (AllowedRows Γ)
      (allowed_rows_nonempty Γ hfin) (allowed_rows_restrict Γ)
    refine ⟨v, fun A hA => ?_⟩
    have h := hv (atoms A) A hA (Finset.Subset.refl _)
    have he : eval (extendRow (atoms A) (fun i => v i)) A = eval v A := by
      apply eval_congr
      intro a ha
      simp [extendRow, ha]
    change eval v A = true
    rw [← he]
    exact h

theorem empty_theory_satisfiable {α : Type u} [_atomDecidable : DecidableEq α] : TheorySatisfiable (∅ : Theory α) := by
  exact ⟨fun _ => false, fun A hA => hA.elim⟩

theorem finite_unsatisfiable_obstruction (Γ : Theory α) :
    ¬ TheorySatisfiable Γ ↔
      ∃ Δ : Finset (PropFormula α), (↑Δ : Set (PropFormula α)) ⊆ Γ ∧ ¬ Satisfiable Δ := by
  classical
  constructor
  · intro h
    have hn : ¬ FiniteSatisfiable Γ := fun hf => h ((compactness Γ).mpr hf)
    simpa [FiniteSatisfiable, not_forall, not_imp] using hn
  · rintro ⟨Δ, hΔ, hn⟩ ⟨v, hv⟩
    exact hn ⟨v, fun A hA => hv A (hΔ hA)⟩

theorem entails_iff_negation_unsatisfiable {α : Type u} [_atomDecidable : DecidableEq α]
    (Γ : Theory α) (C : PropFormula α) :
    TheoryEntails Γ C ↔ ¬ TheorySatisfiable (insert (.neg C) Γ) := by
  constructor
  · intro h ⟨v, hv⟩
    have hC := h v (fun A hA => hv A (Set.mem_insert_of_mem _ hA))
    have hn := hv (.neg C) (Set.mem_insert _ _)
    simp [Satisfies, eval, show eval v C = true from hC] at hn
  · intro hn v hv
    cases he : eval v C with
    | true => exact he
    | false =>
      exfalso
      apply hn
      refine ⟨v, fun A hA => ?_⟩
      rcases Set.mem_insert_iff.mp hA with rfl | hA
      · simp [Satisfies, eval, he]
      · exact hv A hA

theorem finite_semantic_support (Γ : Theory α) (C : PropFormula α) :
    TheoryEntails Γ C ↔
      ∃ Δ : Finset (PropFormula α), (↑Δ : Set (PropFormula α)) ⊆ Γ ∧ Entails Δ C := by
  classical
  constructor
  · intro h
    obtain ⟨Θ, hΘ, hunsat⟩ := (finite_unsatisfiable_obstruction _).mp
      ((entails_iff_negation_unsatisfiable Γ C).mp h)
    let Δ := Θ.filter (fun A => A ∈ Γ)
    have hΔ : (↑Δ : Set (PropFormula α)) ⊆ Γ := by
      intro A hA
      exact (Finset.mem_filter.mp hA).2
    refine ⟨Δ, hΔ, fun v hv => ?_⟩
    cases he : eval v C with
    | true => exact he
    | false =>
      exfalso
      apply hunsat
      refine ⟨v, fun A hA => ?_⟩
      rcases Set.mem_insert_iff.mp (hΘ hA) with rfl | hΓ
      · simp [Satisfies, eval, he]
      · exact hv A (Finset.mem_filter.mpr ⟨hA, hΓ⟩)
  · rintro ⟨Δ, hΔ, h⟩ v hv
    exact h v (fun A hA => hv A (hΔ hA))

/-- Derivability from arbitrary premises still uses a finite proof in the same calculus. -/
def TheoryDerives (Γ : Theory α) (C : PropFormula α) : Prop :=
  ∃ Δ : Finset (PropFormula α), (↑Δ : Set (PropFormula α)) ⊆ Γ ∧ Derives Δ C

def TheoryConsistent (Γ : Theory α) : Prop :=
  ¬ TheoryDerives Γ .falsum

theorem theory_derives_finset (Γ : Finset (PropFormula α)) (C : PropFormula α) :
    TheoryDerives (↑Γ) C ↔ Derives Γ C := by
  constructor
  · rintro ⟨Δ, hΔ, h⟩
    exact h.weaken hΔ
  · intro h
    exact ⟨Γ, Set.Subset.refl _, h⟩

theorem strong_completeness (Γ : Theory α) (C : PropFormula α) :
    TheoryEntails Γ C ↔ TheoryDerives Γ C := by
  constructor
  · intro h
    obtain ⟨Δ, hΔ, h⟩ := (finite_semantic_support Γ C).mp h
    exact ⟨Δ, hΔ, derives_complete h⟩
  · rintro ⟨Δ, hΔ, h⟩ v hv
    exact derives_sound h v (fun A hA => hv A (hΔ hA))

theorem consistency_iff_satisfiable (Γ : Theory α) :
    TheoryConsistent Γ ↔ TheorySatisfiable Γ := by
  constructor
  · intro hc
    by_contra hn
    apply hc
    apply (strong_completeness Γ .falsum).mp
    intro v hv
    exact (hn ⟨v, hv⟩).elim
  · rintro ⟨v, hv⟩ hd
    have h := (strong_completeness Γ .falsum).mpr hd v hv
    exact Bool.false_ne_true h

end Lemmatheca.MathematicalLogic.PropositionalCompactness
