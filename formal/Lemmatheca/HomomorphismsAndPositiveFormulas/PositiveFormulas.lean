import Mathlib.ModelTheory.Complexity
import Lemmatheca.DiagramsAndExtensions.Diagrams

/-! Positive existential formulas in the shared first-order syntax. -/
namespace Lemmatheca.ModelTheory.PositiveHomomorphisms
open FirstOrder FirstOrder.Language

universe u v w w' u' v'
variable {L : Language.{u, v}} {α : Type u'} {β : Type v'}

/-- Exactly the atomic, truth, falsity, conjunction, disjunction and existential constructors. -/
inductive IsExistentialPositive : {n : ℕ} → L.BoundedFormula α n → Prop
  | atomic {n} {φ : L.BoundedFormula α n} (h : φ.IsAtomic) : IsExistentialPositive φ
  | top {n} : IsExistentialPositive (⊤ : L.BoundedFormula α n)
  | bot {n} : IsExistentialPositive (⊥ : L.BoundedFormula α n)
  | inf {n} {φ ψ : L.BoundedFormula α n}
      (hφ : IsExistentialPositive φ) (hψ : IsExistentialPositive ψ) :
      IsExistentialPositive (φ ⊓ ψ)
  | sup {n} {φ ψ : L.BoundedFormula α n}
      (hφ : IsExistentialPositive φ) (hψ : IsExistentialPositive ψ) :
      IsExistentialPositive (φ ⊔ ψ)
  | ex {n} {φ : L.BoundedFormula α (n + 1)} (hφ : IsExistentialPositive φ) :
      IsExistentialPositive φ.ex

/-- A positive quantifier-free conjunction, including the empty conjunction. -/
inductive IsAtomicConjunction {n : ℕ} : L.BoundedFormula α n → Prop
  | atomic {φ} (h : φ.IsAtomic) : IsAtomicConjunction φ
  | top : IsAtomicConjunction ⊤
  | inf {φ ψ} (hφ : IsAtomicConjunction φ) (hψ : IsAtomicConjunction ψ) :
      IsAtomicConjunction (φ ⊓ ψ)

theorem atomicConjunction_positive {n : ℕ} {φ : L.BoundedFormula α n}
    (hφ : IsAtomicConjunction φ) : IsExistentialPositive φ := by
  induction hφ with
  | atomic h => exact .atomic h
  | top => exact .top
  | inf _ _ ih ih' => exact .inf ih ih'

theorem atomicConjunction_quantifierFree {n : ℕ} {φ : L.BoundedFormula α n}
    (hφ : IsAtomicConjunction φ) : φ.IsQF := by
  induction hφ with
  | atomic h => exact h.isQF
  | top => exact .top
  | inf _ _ ih ih' => exact ih.inf ih'

theorem positive_relabel {n m : ℕ} {φ : L.BoundedFormula α n}
    (hφ : IsExistentialPositive φ) (f : α → β ⊕ Fin m) :
    IsExistentialPositive (φ.relabel f) := by
  induction hφ with
  | atomic h => exact .atomic (h.relabel f)
  | top => exact .top
  | bot => exact .bot
  | inf _ _ ih ih' => exact .inf ih ih'
  | sup _ _ ih ih' => exact .sup ih ih'
  | ex _ ih => simpa only [BoundedFormula.relabel_ex] using ih.ex

theorem positive_finite_conjunction {n : ℕ} (s : List (L.BoundedFormula α n))
    (hs : ∀ φ ∈ s, IsExistentialPositive φ) :
    IsExistentialPositive (s.foldr (· ⊓ ·) ⊤) := by
  induction s with
  | nil => exact .top
  | cons φ s ih =>
    exact .inf (hs φ (by simp)) (ih (fun ψ hψ => hs ψ (by simp [hψ])))

theorem positive_finite_disjunction {n : ℕ} (s : List (L.BoundedFormula α n))
    (hs : ∀ φ ∈ s, IsExistentialPositive φ) :
    IsExistentialPositive (s.foldr (· ⊔ ·) ⊥) := by
  induction s with
  | nil => exact .bot
  | cons φ s ih =>
    exact .sup (hs φ (by simp)) (ih (fun ψ hψ => hs ψ (by simp [hψ])))

theorem positive_iExs {φ : L.Formula (α ⊕ β)} [Finite β]
    (hφ : IsExistentialPositive φ) : IsExistentialPositive (φ.iExs β) := by
  have exs_positive : ∀ {n} {θ : L.BoundedFormula α n},
      IsExistentialPositive θ → IsExistentialPositive θ.exs := by
    intro n
    induction n with
    | zero => exact fun h => h
    | succ n ih => exact fun h => ih h.ex
  unfold Formula.iExs
  apply exs_positive
  exact positive_relabel hφ _

/-- Existential closure of exactly the displayed finite free-variable tuple. -/
noncomputable def existentialClosure {n : ℕ} (φ : L.Formula (Fin n)) : L.Sentence :=
  (φ.relabel (Sum.inr : Fin n → Empty ⊕ Fin n)).iExs (Fin n)

theorem existentialClosure_positive {n : ℕ} {φ : L.Formula (Fin n)}
    (hφ : IsExistentialPositive φ) : IsExistentialPositive (existentialClosure φ) := by
  apply positive_iExs
  exact positive_relabel hφ (Sum.inl ∘ Sum.inr)

theorem existentialClosure_realize {M : Type w} [L.Structure M] {n : ℕ}
    (φ : L.Formula (Fin n)) :
    M ⊨ existentialClosure φ ↔ ∃ a : Fin n → M, φ.Realize a := by
  simp only [existentialClosure, Sentence.Realize, Formula.realize_iExs,
    Formula.realize_relabel]
  rfl

/-- The image assignments include the actual image of each chosen quantified witness. -/
theorem hom_preserves_positive {M : Type w} {N : Type w'}
    [L.Structure M] [L.Structure N] {n : ℕ}
    (h : M →[L] N) {φ : L.BoundedFormula α n} (hφ : IsExistentialPositive φ)
    (a : α → M) (xs : Fin n → M) :
    φ.Realize a xs → φ.Realize (h ∘ a) (h ∘ xs) := by
  revert a xs
  induction hφ with
  | atomic hφ => exact Diagrams.hom_preserves_atomic h hφ
  | top => simp
  | bot => simp
  | inf _ _ ih ih' =>
    intro a xs ha
    rw [BoundedFormula.realize_inf] at ha ⊢
    exact ⟨ih a xs ha.1, ih' a xs ha.2⟩
  | sup _ _ ih ih' =>
    intro a xs ha
    rw [BoundedFormula.realize_sup] at ha ⊢
    exact ha.elim (fun hp => Or.inl (ih a xs hp)) (fun hp => Or.inr (ih' a xs hp))
  | ex _ ih =>
    intro a xs ha
    obtain ⟨b, hb⟩ := BoundedFormula.realize_ex.mp ha
    apply BoundedFormula.realize_ex.mpr
    refine ⟨h b, ?_⟩
    simpa only [Fin.comp_snoc] using ih a (Fin.snoc xs b) hb

/-- The positive sentences true in this specific structure. -/
def positiveTheory (M : Type w) [L.Structure M] : L.Theory :=
  {σ | IsExistentialPositive σ ∧ M ⊨ σ}

/-- Sentence preservation over nonempty structures, at any sufficiently large carrier universe. -/
def HomPreserved (σ : L.Sentence) : Prop :=
  ∀ (M N : Theory.ModelType.{u, v, max u v w} (∅ : L.Theory))
    (_h : M →[L] N), M ⊨ σ → N ⊨ σ

/-- All existential-positive semantic consequences on nonempty structures. -/
def positiveConsequences (σ : L.Sentence) : L.Theory :=
  {θ | IsExistentialPositive θ ∧ ({σ} : L.Theory) ⊨ᵇ θ}

end Lemmatheca.ModelTheory.PositiveHomomorphisms
