import Mathlib.ModelTheory.Fraisse
import Mathlib.Data.Fintype.Sets

/-! Finite relational ages, prescribed inclusions, and the size of an age witness. -/

namespace Lemmatheca.ModelTheory.AgesAndAmalgamation

open FirstOrder FirstOrder.Language CategoryTheory
open scoped FirstOrder

universe w

/-- The languages used in the finite-pattern construction have finitely many relation symbols
and no functions, including no constants. -/
def FiniteRelational (L : Language) : Prop :=
  L.IsRelational ∧ Finite (Σ n, L.Relations n)

variable {L : Language}

/-- Membership in the class is independent of the presentation of the underlying finite set. -/
def IsoClosed (K : Set (Bundled L.Structure)) : Prop :=
  ∀ A B : Bundled L.Structure, Nonempty (A ≃[L] B) → (A ∈ K ↔ B ∈ K)

/-- Members have no common finite bound on their sizes. -/
def UnboundedSizes (K : Set (Bundled L.Structure)) : Prop :=
  ∀ n : ℕ, ∃ A ∈ K, Nonempty (Fin n ↪ A)

/-- A structure on a fixed finite carrier is determined by a finite relation truth table. -/
theorem finite_structure_type [L.IsRelational] [Finite (Σ n, L.Relations n)]
    (M : Type*) [Finite M] : Finite (L.Structure M) := by
  classical
  let table : L.Structure M → ((r : Σ n, L.Relations n) → (Fin r.1 → M) → Prop) :=
    fun S r => @Structure.RelMap L M S r.1 r.2
  apply Finite.of_injective table
  intro S T h
  apply Structure.ext
  · funext n f
    exact isEmptyElim f
  · funext n r xs
    exact congrFun (congrFun h ⟨n, r⟩) xs

/-- Relabeling a finite structure onto a finite initial segment gives countably many types. -/
theorem countable_finite_isomorphism_types [L.IsRelational]
    [Finite (Σ n, L.Relations n)] (K : Set (Bundled.{w} L.Structure))
    (hfinite : ∀ A ∈ K, Finite A) : (Quotient.mk' '' K).Countable := by
  classical
  let : ∀ n : ℕ, Finite (L.Structure (ULift.{w} (Fin n))) :=
    fun n => finite_structure_type _
  let f : (Σ n : ℕ, L.Structure (ULift.{w} (Fin n))) →
      Quotient (Language.equivSetoid (L := L)) :=
    fun p => Quotient.mk' (Bundled.mk (ULift.{w} (Fin p.1)) p.2)
  apply (Set.countable_range f).mono
  rintro _ ⟨A, hA, rfl⟩
  let : Finite A := hfinite A hA
  let : Fintype A := Fintype.ofFinite A
  let e : A ≃ ULift.{w} (Fin (Fintype.card A)) :=
    (Fintype.equivFin A).trans Equiv.ulift.symm
  refine ⟨⟨Fintype.card A, (e.bundledInduced L).str⟩, ?_⟩
  change Quotient.mk' (e.bundledInduced L) = Quotient.mk' A
  exact Quotient.sound ⟨(e.bundledInducedEquiv L).symm⟩

variable {A B : Type} [L.Structure A] [L.Structure B]

/-- Keep the old carrier as a left summand and label the points outside its image separately. -/
noncomputable def copyEquiv (f : A ↪[L] B) :
    (A ⊕ {b : B // b ∉ Set.range f}) ≃ B := by
  classical
  exact ((Equiv.ofInjective f f.injective).sumCongr (_root_.Equiv.refl _)).trans
    (Equiv.Set.sumCompl (Set.range f))

/-- The relabeling agrees with the specified old embedding on every old point. -/
theorem copyEquiv_old_points (f : A ↪[L] B) (a : A) :
    copyEquiv f (Sum.inl a) = f a := by
  rfl

/-- Transported interpretations make the specified left inclusion an embedding. -/
theorem copy_inclusion (f : A ↪[L] B) :
    letI : L.Structure (A ⊕ {b : B // b ∉ Set.range f}) :=
      (copyEquiv f).symm.inducedStructure
    ∃ j : A ↪[L] (A ⊕ {b : B // b ∉ Set.range f}),
      (j : A → A ⊕ {b : B // b ∉ Set.range f}) = Sum.inl := by
  let : L.Structure (A ⊕ {b : B // b ∉ Set.range f}) :=
    (copyEquiv f).symm.inducedStructure
  refine ⟨(copyEquiv f).symm.inducedStructureEquiv.toEmbedding.comp f, ?_⟩
  funext a
  change (copyEquiv f).symm (f a) = Sum.inl a
  exact (copyEquiv f).symm_apply_eq.mpr (copyEquiv_old_points f a).symm

/-- HP and JEP characterize ages in a finite relational language. The witness may be empty. -/
theorem exists_countable_age_iff [L.IsRelational] [Finite (Σ n, L.Relations n)]
    (K : Set (Bundled L.Structure)) (hne : K.Nonempty) (hiso : IsoClosed K)
    (hfinite : ∀ A ∈ K, Finite A) :
    (∃ M : Bundled L.Structure, Countable M ∧ L.age M = K) ↔
      Hereditary K ∧ JointEmbedding K := by
  let : IsEmpty (Σ n, L.Functions n) := ⟨fun f => isEmptyElim f.2⟩
  rw [exists_countable_is_age_of_iff]
  constructor
  · rintro ⟨_, _, _, _, hp, hj⟩
    exact ⟨hp, hj⟩
  · rintro ⟨hp, hj⟩
    exact ⟨hne, hiso, countable_finite_isomorphism_types K hfinite,
      fun A hA => Structure.fg_iff_finite.mpr (hfinite A hA), hp, hj⟩

variable (L) (M : Type) [L.Structure M]

/-- The age detects whether its ambient carrier has a point. -/
theorem age_nonempty_carrier [L.IsRelational] :
    Nonempty M ↔ ∃ A ∈ L.age M, Nonempty A := by
  constructor
  · rintro ⟨m⟩
    let S := Substructure.closure L ({m} : Set M)
    have hS : S.FG := Substructure.fg_closure_singleton m
    refine ⟨Bundled.of S, ⟨(Substructure.fg_iff_structure_fg S).1 hS,
      ⟨S.subtype⟩⟩, ⟨⟨m, ?_⟩⟩⟩
    exact Substructure.subset_closure (by simp)
  · rintro ⟨A, ⟨_, ⟨f⟩⟩, ⟨a⟩⟩
    exact ⟨f a⟩

/-- An infinite relational structure has finite induced structures of unbounded sizes. -/
theorem age_unbounded_iff_infinite [L.IsRelational] :
    UnboundedSizes (L.age M) ↔ Infinite M := by
  classical
  constructor
  · intro h
    by_contra hn
    let : Finite M := not_infinite_iff_finite.mp hn
    let : Fintype M := Fintype.ofFinite M
    obtain ⟨A, hA, ⟨e⟩⟩ := h (Fintype.card M + 1)
    have bound := Fintype.card_le_of_injective
      (hA.2.some ∘ e) (hA.2.some.injective.comp e.injective)
    simp only [Fintype.card_fin] at bound
    omega
  · intro hM n
    let : Infinite M := hM
    let e : Fin n ↪ M := Fin.valEmbedding.trans (Infinite.natEmbedding M)
    let S := Substructure.closure L (Set.range e)
    have hS : S.FG := Substructure.fg_closure (Set.finite_range e)
    refine ⟨Bundled.of S, ⟨(Substructure.fg_iff_structure_fg S).1 hS,
      ⟨S.subtype⟩⟩, ⟨?_⟩⟩
    exact ⟨fun i => ⟨e i, Substructure.subset_closure (Set.mem_range_self i)⟩,
      fun i j h => e.injective (congrArg Subtype.val h)⟩

end Lemmatheca.ModelTheory.AgesAndAmalgamation
