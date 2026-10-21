import Lemmatheca.FirstOrderStructures.FirstOrderSemantics
import Mathlib.Basic.Countable.Basic

/-! Well-founded countably branching formulas, using the shared finite terms and scopes. -/
namespace Lemmatheca.MathematicalLogic.InfinitaryLogic

open FirstOrder FirstOrder.Language

universe u v w w' z z'

/-- Infinitary formulas with a finite type of free names and finitely many bound slots. -/
inductive Formula (L : Language.{u, v}) (α : Type w) [Finite α] : ℕ → Type (max u v w)
  | falsum {n} : Formula L α n
  | equal {n} (t s : L.Term (α ⊕ Fin n)) : Formula L α n
  | rel {n k} (R : L.Relations k) (ts : Fin k → L.Term (α ⊕ Fin n)) : Formula L α n
  | imp {n} (φ ψ : Formula L α n) : Formula L α n
  | all {n} (φ : Formula L α (n + 1)) : Formula L α n
  | conj {n} (φ : ℕ → Formula L α n) : Formula L α n

variable {L : Language.{u, v}} {α : Type w} {β : Type w'} [Finite α] [Finite β]
  {n : ℕ}

namespace Formula

def neg (φ : Formula L α n) : Formula L α n := .imp φ .falsum
def top : Formula L α n := neg .falsum
def and (φ ψ : Formula L α n) : Formula L α n := neg (.imp φ (neg ψ))
def or (φ ψ : Formula L α n) : Formula L α n := .imp (neg φ) ψ
def ex (φ : Formula L α (n + 1)) : Formula L α n := neg (.all (neg φ))
def iff (φ ψ : Formula L α n) : Formula L α n := and (.imp φ ψ) (.imp ψ φ)
def disj (φ : ℕ → Formula L α n) : Formula L α n := neg (.conj fun i => neg (φ i))

/-- A finite conjunction presented as a sequence padded by truth. -/
def finiteConj (φ : List (Formula L α n)) : Formula L α n :=
  .conj fun i => (φ[i]?).getD top

/-- Rename free names without changing any protected bound slot. -/
def relabel (f : α → β) : {n : ℕ} → Formula L α n → Formula L β n
  | _, .falsum => .falsum
  | _, .equal t s => .equal (t.relabel (Sum.map f id)) (s.relabel (Sum.map f id))
  | _, .rel R ts => .rel R (fun i => (ts i).relabel (Sum.map f id))
  | _, .imp φ ψ => .imp (relabel f φ) (relabel f ψ)
  | _, .all φ => .all (relabel f φ)
  | _, .conj φ => .conj (fun i => relabel f (φ i))

/-- The constructor-by-constructor inclusion of the shared finite first-order syntax. -/
def ofFirstOrder : {n : ℕ} → L.BoundedFormula α n → Formula L α n
  | _, .falsum => .falsum
  | _, .equal t s => .equal t s
  | _, .rel R ts => .rel R ts
  | _, .imp φ ψ => .imp (ofFirstOrder φ) (ofFirstOrder ψ)
  | _, .all φ => .all (ofFirstOrder φ)

theorem ofFirstOrder_injective :
    Function.Injective (ofFirstOrder : L.BoundedFormula α n → Formula L α n) := by
  intro φ
  induction φ with
  | falsum => intro ψ h; cases ψ <;> simp_all [ofFirstOrder]
  | equal t s => intro ψ h; cases ψ <;> simp_all [ofFirstOrder]
  | rel R ts => intro ψ h; cases ψ <;> simp_all [ofFirstOrder]
  | imp φ ψ ihφ ihψ =>
    intro θ h
    cases θ <;> simp only [ofFirstOrder, Formula.imp.injEq, reduceCtorEq] at h
    exact congrArg₂ BoundedFormula.imp (ihφ h.1) (ihψ h.2)
  | all φ ih =>
    intro ψ h
    cases ψ <;> simp only [ofFirstOrder, Formula.all.injEq, reduceCtorEq] at h
    exact congrArg BoundedFormula.all (ih h)

/-- Formula trees may be packed across their different scoped contexts. -/
abbrev Packed (L : Language.{u, v}) (α : Type w) [Finite α] := Σ n, Formula L α n

/-- Children numbered by natural numbers; absent children give no occurrence. -/
def child : Packed L α → ℕ → Option (Packed L α)
  | ⟨_, .falsum⟩, _ => none
  | ⟨_, .equal _ _⟩, _ => none
  | ⟨_, .rel _ _⟩, _ => none
  | ⟨n, .imp φ ψ⟩, i => if i = 0 then some ⟨n, φ⟩ else if i = 1 then some ⟨n, ψ⟩ else none
  | ⟨n, .all φ⟩, i => if i = 0 then some ⟨n + 1, φ⟩ else none
  | ⟨n, .conj φ⟩, i => some ⟨n, φ i⟩

def ImmediateSubformula (φ ψ : Packed L α) : Prop := ∃ i, child ψ i = some φ

theorem wellFounded_subformula : WellFounded (ImmediateSubformula (L := L) (α := α)) := by
  constructor
  rintro ⟨n, φ⟩
  induction φ with
  | falsum =>
    refine Acc.intro _ ?_
    rintro ψ ⟨i, hi⟩
    simp [child] at hi
  | equal t s =>
    refine Acc.intro _ ?_
    rintro ψ ⟨i, hi⟩
    simp [child] at hi
  | rel R ts =>
    refine Acc.intro _ ?_
    rintro ψ ⟨i, hi⟩
    simp [child] at hi
  | imp φ ψ ihφ ihψ =>
    refine Acc.intro _ ?_
    rintro θ ⟨i, hi⟩
    simp only [child] at hi
    split_ifs at hi <;> cases hi
    · exact ihφ
    · exact ihψ
  | all φ ih =>
    refine Acc.intro _ ?_
    rintro ψ ⟨i, hi⟩
    simp only [child] at hi
    split_ifs at hi; cases hi
    exact ih
  | conj φ ih =>
    refine Acc.intro _ ?_
    rintro ψ ⟨i, hi⟩
    simp only [child, Option.some.injEq] at hi
    subst ψ
    exact ih i

/-- An occurrence is a finite path from the root using existing numbered children. -/
def ValidPath (φ : Packed L α) : List ℕ → Prop
  | [] => True
  | i :: p => ∃ ψ, child φ i = some ψ ∧ ValidPath ψ p

def Occurrence (φ : Formula L α n) := {p : List ℕ // ValidPath ⟨n, φ⟩ p}

theorem countable_occurrences (φ : Formula L α n) : Countable (Occurrence φ) := by
  unfold Occurrence
  infer_instance

/-- A bound on the numbers of edges in all root-to-leaf paths. -/
def HeightBound : {n : ℕ} → Formula L α n → ℕ → Prop
  | _, .falsum, _ => True
  | _, .equal _ _, _ => True
  | _, .rel _ _, _ => True
  | _, .imp _ _, 0 => False
  | _, .all _, 0 => False
  | _, .conj _, 0 => False
  | _, .imp φ ψ, h + 1 => HeightBound φ h ∧ HeightBound ψ h
  | _, .all φ, h + 1 => HeightBound φ h
  | _, .conj φ, h + 1 => ∀ i, HeightBound (φ i) h

def quantifierTower (L : Language.{u, v}) (n : ℕ) : ℕ → Formula L Empty n
  | 0 => .falsum
  | k + 1 => .all (quantifierTower L (n + 1) k)

def unboundedDepth (L : Language.{u, v}) : Formula L Empty 0 :=
  .conj (quantifierTower L 0)

private theorem heightBound_tower (L : Language.{u, v}) (n k h : ℕ) :
    HeightBound (quantifierTower L n k) h ↔ k ≤ h := by
  induction k generalizing n h with
  | zero => simp [quantifierTower, HeightBound]
  | succ k ih =>
    cases h <;> simp [quantifierTower, HeightBound, ih]

theorem unboundedDepth_no_finite_height (L : Language.{u, v}) :
    ¬ ∃ h, HeightBound (unboundedDepth L) h := by
  rintro ⟨h, hh⟩
  cases h with
  | zero => exact hh
  | succ h =>
    have hb := (heightBound_tower L 0 (h + 1) h).mp (hh (h + 1))
    omega

end Formula

abbrev Sentence (L : Language.{u, v}) := Formula L Empty 0
abbrev Theory (L : Language.{u, v}) := Set (Sentence L)

/-- Satisfaction uses the unchanged finite-term evaluation and new countable conjunction clause. -/
def Realize {M : Type z} [L.Structure M] :
    {n : ℕ} → Formula L α n → (α → M) → (Fin n → M) → Prop
  | _, .falsum, _, _ => False
  | _, .equal t s, a, b => t.realize (Sum.elim a b) = s.realize (Sum.elim a b)
  | _, .rel R ts, a, b => Structure.RelMap R (fun i => (ts i).realize (Sum.elim a b))
  | _, .imp φ ψ, a, b => Realize φ a b → Realize ψ a b
  | _, .all φ, a, b => ∀ x, Realize φ a (Fin.snoc b x)
  | _, .conj φ, a, b => ∀ i, Realize (φ i) a b

def Sentence.Realize (φ : Sentence L) (M : Type z) [L.Structure M] : Prop :=
  InfinitaryLogic.Realize (M := M) φ Empty.elim Fin.elim0

def Models (M : Type z) [L.Structure M] (T : Theory L) : Prop :=
  ∀ φ ∈ T, Sentence.Realize φ M

def IsSatisfiable (T : Theory L) : Prop :=
  ∃ (M : Type (max u v)) (_ : L.Structure M), Nonempty M ∧ Models M T

def IsFinitelySatisfiable (T : Theory L) : Prop :=
  ∀ F : Finset (Sentence L), (↑F : Set (Sentence L)) ⊆ T → IsSatisfiable (↑F : Theory L)

variable {M : Type z} {N : Type z'} [L.Structure M] [L.Structure N]

theorem realize_neg (φ : Formula L α n) (a : α → M) (b : Fin n → M) :
    Realize φ.neg a b ↔ ¬ Realize φ a b := by
  rfl

theorem realize_abbreviations (φ ψ : Formula L α n) (a : α → M) (b : Fin n → M) :
    (Realize (Formula.top : Formula L α n) a b) ∧
    (Realize (φ.and ψ) a b ↔ Realize φ a b ∧ Realize ψ a b) ∧
    (Realize (φ.or ψ) a b ↔ Realize φ a b ∨ Realize ψ a b) ∧
    (Realize (φ.iff ψ) a b ↔ (Realize φ a b ↔ Realize ψ a b)) := by
  simp only [Formula.top, Formula.and, Formula.or, Formula.iff, Formula.neg, Realize]
  tauto

theorem realize_ex (φ : Formula L α (n + 1)) (a : α → M) (b : Fin n → M) :
    Realize φ.ex a b ↔ ∃ x : M, Realize φ a (Fin.snoc b x) := by
  change (¬ ∀ x : M, ¬ Realize φ a (Fin.snoc b x)) ↔ _
  simp

theorem realize_disj (φ : ℕ → Formula L α n) (a : α → M) (b : Fin n → M) :
    Realize (Formula.disj φ) a b ↔ ∃ i, Realize (φ i) a b := by
  change (¬ ∀ i, ¬ Realize (φ i) a b) ↔ _
  simp

theorem realize_finiteConj (φ : List (Formula L α n)) (a : α → M) (b : Fin n → M) :
    Realize (Formula.finiteConj φ) a b ↔ ∀ ψ ∈ φ, Realize ψ a b := by
  change (∀ i, Realize ((φ[i]?).getD Formula.top) a b) ↔ _
  constructor
  · intro h ψ hψ
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hψ
    simpa [hi] using h i
  · intro h i
    cases hi : φ[i]? with
    | none => simpa using (realize_abbreviations (Formula.falsum : Formula L α n)
        .falsum a b).1
    | some ψ => simpa using h ψ (List.mem_iff_getElem?.mpr ⟨i, hi⟩)

theorem realize_relabel (f : α → β) (φ : Formula L α n) (a : β → M) (b : Fin n → M) :
    Realize (φ.relabel f) a b ↔ Realize φ (a ∘ f) b := by
  induction φ with
  | falsum => rfl
  | equal t s =>
    simp only [Formula.relabel, Realize, Term.realize_relabel]
    have he : Sum.elim a b ∘ Sum.map f id = Sum.elim (a ∘ f) b := by
      funext x
      cases x <;> rfl
    rw [he]
  | rel R ts =>
    simp only [Formula.relabel, Realize, Term.realize_relabel]
    have he : Sum.elim a b ∘ Sum.map f id = Sum.elim (a ∘ f) b := by
      funext x
      cases x <;> rfl
    rw [he]
  | imp φ ψ ihφ ihψ => simp only [Formula.relabel, Realize, ihφ, ihψ]
  | all φ ih =>
    simp only [Formula.relabel, Realize]
    exact forall_congr' fun x => ih (Fin.snoc b x)
  | conj φ ih =>
    simp only [Formula.relabel, Realize]
    exact forall_congr' fun i => ih i b

theorem realize_ofFirstOrder (φ : L.BoundedFormula α n) (a : α → M) (b : Fin n → M) :
    Realize (Formula.ofFirstOrder φ) a b ↔ φ.Realize a b := by
  induction φ with
  | falsum => rfl
  | equal t s => rfl
  | rel R ts => rfl
  | imp φ ψ ihφ ihψ => simp only [Formula.ofFirstOrder, Realize, BoundedFormula.Realize, ihφ, ihψ]
  | all φ ih =>
    simp only [Formula.ofFirstOrder, Realize, BoundedFormula.Realize]
    exact forall_congr' fun x => ih (Fin.snoc b x)

/-- Every shared first-order formula can be viewed in the finite context of its free support. -/
theorem realize_ofFirstOrder_restrict {γ : Type w'} [DecidableEq γ]
    (φ : L.BoundedFormula γ n) (a : γ → M) (b : Fin n → M) :
    Realize (Formula.ofFirstOrder (φ.restrictFreeVar id)) (fun x => a x) b ↔
      φ.Realize a b := by
  rw [realize_ofFirstOrder]
  exact BoundedFormula.realize_restrictFreeVar a (fun _ => rfl)

theorem realize_isomorphism (e : M ≃[L] N) (φ : Formula L α n)
    (a : α → M) (b : Fin n → M) :
    Realize φ (e ∘ a) (e ∘ b) ↔ Realize φ a b := by
  induction φ with
  | falsum => rfl
  | equal t s =>
    simp only [Realize, ← Sum.comp_elim, HomClass.realize_term,
      EmbeddingLike.apply_eq_iff_eq e]
  | rel R ts =>
    simp only [Realize, ← Sum.comp_elim, HomClass.realize_term]
    exact StrongHomClass.map_rel e _ _
  | imp φ ψ ihφ ihψ => simp only [Realize, ihφ, ihψ]
  | all φ ih =>
    simp only [Realize]
    constructor
    · intro h x
      have hx := h (e x)
      rw [← Fin.comp_snoc, ih] at hx
      exact hx
    · intro h x
      have hx := h (e.symm x)
      rw [← ih, Fin.comp_snoc, e.apply_symm_apply] at hx
      exact hx
  | conj φ ih =>
    simp only [Realize]
    exact forall_congr' fun i => ih i b

theorem sentence_isomorphism (e : M ≃[L] N) (φ : Sentence L) :
    Sentence.Realize φ M ↔ Sentence.Realize φ N := by
  have h := realize_isomorphism e φ Empty.elim Fin.elim0
  have ha : e ∘ (Empty.elim : Empty → M) = Empty.elim := by
    funext x
    exact x.elim
  have hb : e ∘ (Fin.elim0 : Fin 0 → M) = Fin.elim0 := by
    funext x
    exact x.elim0
  simpa only [Sentence.Realize, ha, hb] using h.symm

end Lemmatheca.MathematicalLogic.InfinitaryLogic
