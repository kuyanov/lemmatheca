import Lemmatheca.PreservationConverses.PreservationUniversal
import Lemmatheca.InductiveTheories.ExistentialReflection

/-! Universal-existential prefixes in the corpus's actual shared syntax. -/
namespace Lemmatheca.ModelTheory.InductiveTheories
open FirstOrder FirstOrder.Language
open Lemmatheca.ModelTheory
universe u v w w'
variable {L : Language.{u, v}}

/-- A finite universal prefix followed by an existential prefix and a quantifier-free matrix. -/
inductive IsUniversalExistential {α : Type w'} :
    ∀ {n : ℕ}, L.BoundedFormula α n → Prop
  | of_existential {n} {φ : L.BoundedFormula α n} (h : φ.IsExistential) :
      IsUniversalExistential φ
  | all {n} {φ : L.BoundedFormula α (n + 1)} (h : IsUniversalExistential φ) :
      IsUniversalExistential φ.all

/-- The chosen axiom set itself has the displayed universal-existential prefix form. -/
def IsUniversalExistentialTheory (T : L.Theory) : Prop :=
  ∀ σ ∈ T, IsUniversalExistential σ

/-- Semantic reaxiomatization, rather than membership of the originally written axioms. -/
def HasUniversalExistentialAxiomatization (T : L.Theory) : Prop :=
  ∃ U : L.Theory, IsUniversalExistentialTheory U ∧ Theories.Equivalent T U

/-- All universal-existential semantic consequences, in the original language. -/
def universalExistentialPart (T : L.Theory) : L.Theory :=
  {σ | IsUniversalExistential σ ∧ T ⊨ᵇ σ}

/-- True universal sentences in the canonically named expansion. -/
def universalDiagram (L : Language.{u, v}) (M : Type w) [L.Structure M] : L[[M]].Theory :=
  {σ | σ.IsUniversal ∧ M ⊨ σ}

/-- Universal formulas are a boundary case with an empty existential block. -/
theorem universal_isUniversalExistential {α : Type w'} {n : ℕ}
    {φ : L.BoundedFormula α n} (h : φ.IsUniversal) : IsUniversalExistential φ := by
  induction h with
  | of_isQF hq => exact .of_existential hq.isExistential
  | all _ ih => exact .all ih

private theorem prefix_castLE {α : Type w'} {m : ℕ} {φ : L.BoundedFormula α m}
    (hφ : IsUniversalExistential φ) :
    ∀ {n} {h : m ≤ n}, IsUniversalExistential (φ.castLE h) :=
  IsUniversalExistential.recOn
    (motive := @fun m φ _ => ∀ (n : ℕ) (h : m ≤ n),
      IsUniversalExistential (φ.castLE h)) hφ
    (@fun _ _ he _ _ => .of_existential (Preservation.existential_castLE he))
    (@fun _ _ _ ih _ _ => (ih _ _).all) _ _

private theorem prefix_liftAt {α : Type w'} {m : ℕ} {φ : L.BoundedFormula α m}
    (hφ : IsUniversalExistential φ) {k n : ℕ} :
    IsUniversalExistential (φ.liftAt k n) :=
  IsUniversalExistential.recOn hφ
    (fun he => .of_existential (Preservation.existential_liftAt he))
    (fun _ ih => (prefix_castLE ih).all)

private theorem prefix_binary {α : Type w'} {m : ℕ}
    {φ ψ : L.BoundedFormula α m} (hφ : IsUniversalExistential φ)
    (hψ : IsUniversalExistential ψ) (b : Bool) :
    ∃ χ : L.BoundedFormula α m, IsUniversalExistential χ ∧
      ∀ (M : Type w) [L.Structure M] [Nonempty M] (v : α → M) (xs : Fin m → M),
        χ.Realize v xs ↔
          if b then φ.Realize v xs ∧ ψ.Realize v xs else φ.Realize v xs ∨ ψ.Realize v xs := by
  classical
  induction hφ with
  | @of_existential m φ he =>
    induction hψ with
    | @of_existential m ψ he' =>
      obtain ⟨χ, hχ, hχr⟩ := Preservation.exists_existential_binary he he' b
      exact ⟨χ, .of_existential hχ, hχr⟩
    | @all m ψ hp ih =>
      obtain ⟨χ, hχ, hr⟩ := ih (φ := φ.liftAt 1 m) (Preservation.existential_liftAt he)
      refine ⟨χ.all, hχ.all, ?_⟩
      intro M _ _ v xs
      rw [BoundedFormula.realize_all]
      refine (forall_congr' fun x => hr M v (Fin.snoc xs x)).trans ?_
      cases b <;> simp [BoundedFormula.realize_all, forall_and]
      by_cases hh : φ.Realize v xs <;> simp [hh]
  | @all m φ hp ih =>
    obtain ⟨χ, hχ, hr⟩ := ih (ψ := ψ.liftAt 1 m) (prefix_liftAt hψ)
    refine ⟨χ.all, hχ.all, ?_⟩
    intro M _ _ v xs
    rw [BoundedFormula.realize_all]
    refine (forall_congr' fun x => hr M v (Fin.snoc xs x)).trans ?_
    cases b <;> simp [BoundedFormula.realize_all, forall_and]
    by_cases hh : ψ.Realize v xs <;> simp [hh]

/-- Conjunction has an equivalent actual universal-existential prefix, in any finite bound context. -/
theorem universalExistential_conjunction {α : Type w'} {n : ℕ}
    {φ ψ : L.BoundedFormula α n} (hφ : IsUniversalExistential φ)
    (hψ : IsUniversalExistential ψ) :
    ∃ χ : L.BoundedFormula α n, IsUniversalExistential χ ∧
      ∀ (M : Type w) [L.Structure M] [Nonempty M] (v : α → M) (a : Fin n → M),
        χ.Realize v a ↔ φ.Realize v a ∧ ψ.Realize v a := by
  simpa using prefix_binary hφ hψ true

/-- Disjunction has an equivalent actual universal-existential prefix. -/
theorem universalExistential_disjunction {α : Type w'} {n : ℕ}
    {φ ψ : L.BoundedFormula α n} (hφ : IsUniversalExistential φ)
    (hψ : IsUniversalExistential ψ) :
    ∃ χ : L.BoundedFormula α n, IsUniversalExistential χ ∧
      ∀ (M : Type w) [L.Structure M] [Nonempty M] (v : α → M) (a : Fin n → M),
        χ.Realize v a ↔ φ.Realize v a ∨ ψ.Realize v a := by
  simpa using prefix_binary hφ hψ false

/-- This diagram includes every true signed atomic fact, not just positive facts. -/
theorem signedDiagram_subset_universalDiagram (M : Type w) [L.Structure M] :
    Diagrams.signedDiagram L M ⊆ universalDiagram L M := by
  rintro σ ⟨hσ, ht⟩
  refine ⟨?_, ht⟩
  rcases hσ with ha | ⟨θ, hθ, rfl⟩
  · exact ha.isQF.isUniversal
  · exact hθ.isQF.not.isUniversal

/-- Each model satisfies the particular universal-existential part of its theory. -/
theorem model_universalExistentialPart (T : L.Theory) (M : Type w)
    [L.Structure M] [Nonempty M] [M ⊨ T] : M ⊨ universalExistentialPart T := by
  exact ⟨fun _ hσ => hσ.2.realize_sentence M⟩

end Lemmatheca.ModelTheory.InductiveTheories
