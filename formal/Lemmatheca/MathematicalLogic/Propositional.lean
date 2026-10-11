import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi

/-! Finite propositional syntax, Boolean semantics, substitution, and truth tables.

The atom type is arbitrary. Finite supports and the executable table checks use
decidable equality of atoms. Finite contexts are finsets; rows are functions from
the finite support subtype to Bool. No infinite-premise compactness is asserted.
-/

namespace Lemmatheca.MathematicalLogic

universe u v

inductive PropFormula (α : Type u) : Type u
  | atom : α → PropFormula α
  | falsum : PropFormula α
  | neg : PropFormula α → PropFormula α
  | conj : PropFormula α → PropFormula α → PropFormula α
  | disj : PropFormula α → PropFormula α → PropFormula α
  | impl : PropFormula α → PropFormula α → PropFormula α
  deriving DecidableEq

abbrev Valuation (α : Type u) := α → Bool

def verum {α : Type u} : PropFormula α := .neg .falsum

def biconditional {α : Type u} (A B : PropFormula α) : PropFormula α :=
  .conj (.impl A B) (.impl B A)

def height {α : Type u} : PropFormula α → ℕ
  | .atom _ => 0
  | .falsum => 0
  | .neg A => 1 + height A
  | .conj A B | .disj A B | .impl A B => 1 + max (height A) (height B)

def eval {α : Type u} (v : Valuation α) : PropFormula α → Bool
  | .atom a => v a
  | .falsum => false
  | .neg A => !(eval v A)
  | .conj A B => eval v A && eval v B
  | .disj A B => eval v A || eval v B
  | .impl A B => !(eval v A) || eval v B

theorem eval_unique {α : Type u} (v : Valuation α) (E : PropFormula α → Bool)
    (hAtom : ∀ a, E (.atom a) = v a)
    (hFalsum : E .falsum = false)
    (hNeg : ∀ A, E (.neg A) = !(E A))
    (hConj : ∀ A B, E (.conj A B) = (E A && E B))
    (hDisj : ∀ A B, E (.disj A B) = (E A || E B))
    (hImpl : ∀ A B, E (.impl A B) = (!(E A) || E B)) :
    ∀ A, E A = eval v A := by
  intro A
  induction A <;> simp_all [eval]

def Satisfies {α : Type u} (v : Valuation α) (A : PropFormula α) : Prop :=
  eval v A = true

def SatisfiesContext {α : Type u} (v : Valuation α) (Γ : Finset (PropFormula α)) : Prop :=
  ∀ B ∈ Γ, Satisfies v B

def Tautology {α : Type u} (A : PropFormula α) : Prop :=
  ∀ v, Satisfies v A

def Contradiction {α : Type u} (A : PropFormula α) : Prop :=
  ∀ v, eval v A = false

def SemEquivalent {α : Type u} (A B : PropFormula α) : Prop :=
  ∀ v, eval v A = eval v B

def Satisfiable {α : Type u} (Γ : Finset (PropFormula α)) : Prop :=
  ∃ v, SatisfiesContext v Γ

def Entails {α : Type u} (Γ : Finset (PropFormula α)) (A : PropFormula α) : Prop :=
  ∀ v, SatisfiesContext v Γ → Satisfies v A

def Countervaluation {α : Type u} (v : Valuation α)
    (Γ : Finset (PropFormula α)) (A : PropFormula α) : Prop :=
  SatisfiesContext v Γ ∧ eval v A = false

theorem tautology_verum {α : Type u} : Tautology (verum : PropFormula α) := by
  intro v
  rfl

theorem not_entails_iff_countervaluation {α : Type u}
    (Γ : Finset (PropFormula α)) (A : PropFormula α) :
    ¬ Entails Γ A ↔ ∃ v, Countervaluation v Γ A := by
  classical
  constructor
  · intro h
    by_contra hn
    apply h
    intro v hv
    change eval v A = true
    cases he : eval v A with
    | false => exact (hn ⟨v, hv, he⟩).elim
    | true => rfl
  · rintro ⟨v, hv, hA⟩ h
    have ht := h v hv
    simp only [Satisfies, hA, Bool.false_eq_true] at ht

theorem entails_empty_iff {α : Type u} (A : PropFormula α) :
    Entails ∅ A ↔ Tautology A := by
  simp [Entails, SatisfiesContext, Tautology]

theorem unsatisfiable_entails {α : Type u} (Γ : Finset (PropFormula α))
    (hΓ : ¬ Satisfiable Γ) (A : PropFormula α) : Entails Γ A := by
  intro v hv
  exact (hΓ ⟨v, hv⟩).elim

theorem entails_singleton_iff_tautology {α : Type u} (A B : PropFormula α) :
    Entails {A} B ↔ Tautology (.impl A B) := by
  constructor
  · intro h v
    have hh := h v
    cases ha : eval v A <;> cases hb : eval v B <;>
      simp_all [Satisfies, eval, SatisfiesContext]
  · intro h v hv
    have ha := hv A (Finset.mem_singleton_self A)
    have hh := h v
    simpa [Satisfies, eval, show eval v A = true from ha] using hh

def atoms {α : Type u} [DecidableEq α] : PropFormula α → Finset α
  | .atom a => {a}
  | .falsum => ∅
  | .neg A => atoms A
  | .conj A B | .disj A B | .impl A B => atoms A ∪ atoms B

def contextAtoms {α : Type u} [DecidableEq α] (Γ : Finset (PropFormula α)) : Finset α :=
  Γ.biUnion atoms

theorem eval_congr {α : Type u} [DecidableEq α] (A : PropFormula α)
    (v w : Valuation α) (h : ∀ a ∈ atoms A, v a = w a) :
    eval v A = eval w A := by
  induction A generalizing v w with
  | atom a => exact h a (Finset.mem_singleton_self a)
  | falsum => rfl
  | neg A ih =>
    change ∀ a ∈ atoms A, v a = w a at h
    simp only [eval, ih v w h]
  | conj A B ihA ihB | disj A B ihA ihB | impl A B ihA ihB =>
    simp only [atoms, Finset.mem_union] at h
    simp only [eval, ihA v w (fun a ha => h a (Or.inl ha)),
      ihB v w (fun a ha => h a (Or.inr ha))]

theorem countervaluation_congr {α : Type u} [DecidableEq α]
    (Γ : Finset (PropFormula α)) (A : PropFormula α) (v w : Valuation α)
    (h : ∀ a ∈ contextAtoms Γ ∪ atoms A, v a = w a) :
    Countervaluation v Γ A ↔ Countervaluation w Γ A := by
  have hE : ∀ B ∈ Γ, eval v B = eval w B := by
    intro B hB
    apply eval_congr
    intro a ha
    apply h
    exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨B, hB, ha⟩)
  have hA : eval v A = eval w A :=
    eval_congr A v w (fun a ha => h a (Finset.mem_union_right _ ha))
  unfold Countervaluation SatisfiesContext Satisfies
  constructor
  · rintro ⟨hv, hf⟩
    exact ⟨fun B hB => (hE B hB) ▸ hv B hB, hA ▸ hf⟩
  · rintro ⟨hw, hf⟩
    exact ⟨fun B hB => (hE B hB).symm ▸ hw B hB, hA.symm ▸ hf⟩

def subst {α : Type u} {β : Type v} (σ : α → PropFormula β) :
    PropFormula α → PropFormula β
  | .atom a => σ a
  | .falsum => .falsum
  | .neg A => .neg (subst σ A)
  | .conj A B => .conj (subst σ A) (subst σ B)
  | .disj A B => .disj (subst σ A) (subst σ B)
  | .impl A B => .impl (subst σ A) (subst σ B)

def substContext {α : Type u} {β : Type v} [DecidableEq β]
    (σ : α → PropFormula β) (Γ : Finset (PropFormula α)) : Finset (PropFormula β) :=
  Γ.image (subst σ)

theorem eval_subst {α : Type u} {β : Type v} (σ : α → PropFormula β)
    (w : Valuation β) (A : PropFormula α) :
    eval w (subst σ A) = eval (fun a => eval w (σ a)) A := by
  induction A <;> simp_all [subst, eval]

theorem subst_tautology {α : Type u} {β : Type v} (σ : α → PropFormula β)
    (A : PropFormula α) (hA : Tautology A) : Tautology (subst σ A) := by
  intro w
  change eval w (subst σ A) = true
  rw [eval_subst]
  exact hA _

theorem subst_entails {α : Type u} {β : Type v} [DecidableEq β]
    (σ : α → PropFormula β) (Γ : Finset (PropFormula α)) (A : PropFormula α)
    (h : Entails Γ A) : Entails (substContext σ Γ) (subst σ A) := by
  intro w hw
  change eval w (subst σ A) = true
  rw [eval_subst]
  apply h
  intro B hB
  have hb := hw (subst σ B) (Finset.mem_image.mpr ⟨B, hB, rfl⟩)
  simpa only [Satisfies, eval_subst] using hb

def truthTableRows {α : Type u} [DecidableEq α] (s : Finset α) : Finset (s → Bool) :=
  Finset.univ

def extendRow {α : Type u} [DecidableEq α] (s : Finset α)
    (r : s → Bool) : Valuation α :=
  fun a => if h : a ∈ s then r ⟨a, h⟩ else false

def tableSupport {α : Type u} [DecidableEq α]
    (Γ : Finset (PropFormula α)) (A : PropFormula α) : Finset α :=
  contextAtoms Γ ∪ atoms A

def TableEntails {α : Type u} [DecidableEq α]
    (Γ : Finset (PropFormula α)) (A : PropFormula α) : Prop :=
  ∀ r : tableSupport Γ A → Bool, EntailsAtRow Γ A r
where
  EntailsAtRow (Γ : Finset (PropFormula α)) (A : PropFormula α)
      (r : tableSupport Γ A → Bool) : Prop :=
    SatisfiesContext (extendRow (tableSupport Γ A) r) Γ →
      Satisfies (extendRow (tableSupport Γ A) r) A

def counterRows {α : Type u} [DecidableEq α]
    (Γ : Finset (PropFormula α)) (A : PropFormula α) :
    Finset (tableSupport Γ A → Bool) :=
  (truthTableRows (tableSupport Γ A)).filter fun r =>
    (∀ B ∈ Γ, eval (extendRow (tableSupport Γ A) r) B = true) ∧
      eval (extendRow (tableSupport Γ A) r) A = false

def checkEntails {α : Type u} [DecidableEq α]
    (Γ : Finset (PropFormula α)) (A : PropFormula α) : Bool :=
  decide (counterRows Γ A = ∅)

def checkSatisfiable {α : Type u} [DecidableEq α]
    (Γ : Finset (PropFormula α)) : Bool :=
  decide (∃ r : contextAtoms Γ → Bool,
    ∀ B ∈ Γ, eval (extendRow (contextAtoms Γ) r) B = true)

def checkTautology {α : Type u} [DecidableEq α] (A : PropFormula α) : Bool :=
  decide (∀ r : atoms A → Bool, eval (extendRow (atoms A) r) A = true)

def checkEquivalent {α : Type u} [DecidableEq α] (A B : PropFormula α) : Bool :=
  decide (∀ r : (↥(atoms A ∪ atoms B) → Bool),
    eval (extendRow (atoms A ∪ atoms B) r) A = eval (extendRow (atoms A ∪ atoms B) r) B)

private theorem eval_extend_restrict {α : Type u} [DecidableEq α]
    (s : Finset α) (v : Valuation α) (A : PropFormula α) (h : atoms A ⊆ s) :
    eval (extendRow s (fun a => v a)) A = eval v A := by
  apply eval_congr
  intro a ha
  simp [extendRow, h ha]

theorem entails_iff_table {α : Type u} [DecidableEq α]
    (Γ : Finset (PropFormula α)) (A : PropFormula α) :
    Entails Γ A ↔ TableEntails Γ A := by
  constructor
  · intro h r
    exact h _
  · intro h v hv
    let r : tableSupport Γ A → Bool := fun a => v a
    have hr : SatisfiesContext (extendRow (tableSupport Γ A) r) Γ := by
      intro B hB
      change eval (extendRow (tableSupport Γ A) r) B = true
      rw [eval_extend_restrict]
      · exact hv B hB
      · intro a ha
        exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨B, hB, ha⟩)
    have hA := h r hr
    change eval v A = true
    rw [← eval_extend_restrict (tableSupport Γ A) v A (fun a ha =>
      Finset.mem_union_right _ ha)]
    exact hA

theorem mem_counterRows {α : Type u} [DecidableEq α]
    (Γ : Finset (PropFormula α)) (A : PropFormula α)
    (r : tableSupport Γ A → Bool) :
    r ∈ counterRows Γ A ↔ Countervaluation (extendRow (tableSupport Γ A) r) Γ A := by
  simp [counterRows, truthTableRows, Countervaluation, SatisfiesContext, Satisfies]

theorem checkEntails_eq_true {α : Type u} [DecidableEq α]
    (Γ : Finset (PropFormula α)) (A : PropFormula α) :
    checkEntails Γ A = true ↔ Entails Γ A := by
  simp only [checkEntails, decide_eq_true_eq]
  constructor
  · intro hc
    apply (entails_iff_table Γ A).mpr
    intro r hr
    change eval (extendRow (tableSupport Γ A) r) A = true
    cases he : eval (extendRow (tableSupport Γ A) r) A with
    | false =>
      have hm := (mem_counterRows Γ A r).mpr ⟨hr, he⟩
      rw [hc] at hm
      exact (Finset.notMem_empty r hm).elim
    | true => rfl
  · intro h
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro r hr
    rcases (mem_counterRows Γ A r).mp hr with ⟨hv, hf⟩
    have ht := h _ hv
    simp only [Satisfies, hf, Bool.false_eq_true] at ht

theorem checkSatisfiable_eq_true {α : Type u} [DecidableEq α]
    (Γ : Finset (PropFormula α)) :
    checkSatisfiable Γ = true ↔ Satisfiable Γ := by
  simp only [checkSatisfiable, decide_eq_true_eq]
  constructor
  · rintro ⟨r, hr⟩
    exact ⟨extendRow (contextAtoms Γ) r, hr⟩
  · rintro ⟨v, hv⟩
    refine ⟨fun a => v a, ?_⟩
    intro B hB
    rw [eval_extend_restrict]
    · exact hv B hB
    · intro a ha
      exact Finset.mem_biUnion.mpr ⟨B, hB, ha⟩

theorem checkTautology_eq_true {α : Type u} [DecidableEq α] (A : PropFormula α) :
    checkTautology A = true ↔ Tautology A := by
  simp only [checkTautology, decide_eq_true_eq]
  constructor
  · intro h v
    have hv := h (fun a => v a)
    rw [eval_extend_restrict (atoms A) v A (fun _ ha => ha)] at hv
    exact hv
  · intro h r
    exact h _

theorem checkEquivalent_eq_true {α : Type u} [DecidableEq α] (A B : PropFormula α) :
    checkEquivalent A B = true ↔ SemEquivalent A B := by
  simp only [checkEquivalent, decide_eq_true_eq]
  constructor
  · intro h v
    have hv := h (fun a => v a)
    rw [eval_extend_restrict (atoms A ∪ atoms B) v A (fun _ ha =>
      Finset.mem_union_left _ ha),
      eval_extend_restrict (atoms A ∪ atoms B) v B (fun _ hb =>
      Finset.mem_union_right _ hb)] at hv
    exact hv
  · intro h r
    exact h _

theorem modusPonens_entails {α : Type u} [DecidableEq α] (A B : PropFormula α) :
    Entails {A, .impl A B} B := by
  intro v hv
  have ha := hv A (by simp)
  have hi := hv (.impl A B) (by simp)
  simpa [Satisfies, eval, show eval v A = true from ha] using hi

theorem modusPonens_tautology {α : Type u} (A B : PropFormula α) :
    Tautology (.impl (.conj A (.impl A B)) B) := by
  intro v
  change eval v (.impl (.conj A (.impl A B)) B) = true
  cases ha : eval v A <;> cases hb : eval v B <;> simp [eval, ha, hb]

theorem affirmingConsequent_countervaluation {α : Type u} [DecidableEq α]
    (a b : α) (hab : a ≠ b) :
    Countervaluation (fun c => if c = b then true else false)
      {.impl (.atom a) (.atom b), .atom b} (.atom a) := by
  simp [Countervaluation, SatisfiesContext, Satisfies, eval, hab]

theorem affirmingConsequent_neg_countervaluation {α : Type u} [DecidableEq α]
    (a b : α) (_hab : a ≠ b) :
    Countervaluation (fun c => if c = a ∨ c = b then true else false)
      {.impl (.atom a) (.atom b), .atom b} (.neg (.atom a)) := by
  simp [Countervaluation, SatisfiesContext, Satisfies, eval]

theorem subst_swap_imp {α : Type u} [DecidableEq α] (a b : α) (hab : a ≠ b) :
    subst (fun c => if c = a then .atom b else if c = b then .atom a else .atom c)
      (.impl (.atom a) (.atom b)) = .impl (.atom b) (.atom a) := by
  simp [subst, Ne.symm hab]

theorem subst_sequential_imp {α : Type u} [DecidableEq α] (a b : α) (hab : a ≠ b) :
    subst (fun c => if c = b then .atom a else .atom c)
      (subst (fun c => if c = a then .atom b else .atom c)
        (.impl (.atom a) (.atom b))) = .impl (.atom a) (.atom a) := by
  simp [subst, Ne.symm hab]

end Lemmatheca.MathematicalLogic
