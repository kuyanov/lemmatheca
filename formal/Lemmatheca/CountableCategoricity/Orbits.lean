import Lemmatheca.CountableCategoricity.FormulaClasses
import Lemmatheca.OmittingTypes.AmbientModels

/-! Actual automorphism orbits, without defining orbit equality through tuple types. -/
namespace Lemmatheca.ModelTheory.CountableCategoricity

open FirstOrder FirstOrder.Language
open Lemmatheca.ModelTheory.Types

universe u v w
variable {L : Language.{u, v}} {T : L.Theory} {M : Type w} [L.Structure M]

/-- The specified automorphism sends every source coordinate to its target coordinate. -/
def SameOrbit {n : ℕ} (a b : Fin n → M) : Prop :=
  ∃ g : M ≃[L] M, ∀ i, g (a i) = b i

/-- Identity, inverse, and composition establish the orbit equivalence relation. -/
theorem sameOrbit_equivalence (n : ℕ) : Equivalence (SameOrbit (L := L) (M := M) (n := n)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a
    exact ⟨Language.Equiv.refl L M, fun _ => rfl⟩
  · rintro a b ⟨g, hg⟩
    exact ⟨g.symm, fun i => by rw [← hg i]; exact g.symm_apply_apply _⟩
  · rintro a b c ⟨g, hg⟩ ⟨h, hh⟩
    exact ⟨h.comp g, fun i => by change h (g (a i)) = c i; rw [hg, hh]⟩

/-- Quotient tuples by actual whole-model automorphisms. -/
def orbitSetoid (L : Language.{u, v}) (M : Type w) [L.Structure M] (n : ℕ) :
    Setoid (Fin n → M) :=
  ⟨SameOrbit (L := L) (M := M), sameOrbit_equivalence (L := L) (M := M) n⟩

/-- The set of automorphism orbits in the specified finite tuple context. -/
abbrev OrbitClass (L : Language.{u, v}) (M : Type w) [L.Structure M] (n : ℕ) :=
  Quotient (orbitSetoid L M n)

/-- Finitely many actual automorphism orbits for every finite tuple length. -/
def Oligomorphic (L : Language.{u, v}) (M : Type w) [L.Structure M] : Prop :=
  ∀ n, Finite (OrbitClass L M n)

/-- The empty tuple has exactly one orbit. -/
theorem empty_orbit_unique :
    Subsingleton (OrbitClass L M 0) ∧ Nonempty (OrbitClass L M 0) := by
  constructor
  · exact ⟨fun c d => Quotient.inductionOn₂ c d (fun a b => congrArg (Quotient.mk _) (Subsingleton.elim a b))⟩
  · exact ⟨Quotient.mk _ (fun i => Fin.elim0 i)⟩

variable [Nonempty M] [M ⊨ T]

/-- Every actual automorphism orbit consists of tuples with the same complete type. -/
theorem sameOrbit_typeOf {n : ℕ} (a b : Fin n → M) (h : SameOrbit (L := L) a b) :
    T.typeOf a = T.typeOf b := by
  obtain ⟨g, hg⟩ := h
  apply SetLike.ext
  intro γ
  change γ ∈ (T.typeOf a).toTheory ↔ γ ∈ (T.typeOf b).toTheory
  let φ := Formula.equivSentence.symm γ
  have hφ : φ.Realize a ↔ φ.Realize b := by
    have heq : g ∘ a = b := funext hg
    rw [← heq]
    exact (g.toElementaryEmbedding.map_formula φ a).symm
  have hmem : φ ∈ formulas (T.typeOf a) ↔ φ ∈ formulas (T.typeOf b) :=
    Theory.CompleteType.formula_mem_typeOf.trans
      (hφ.trans Theory.CompleteType.formula_mem_typeOf.symm)
  simpa only [φ, formulas, Set.mem_preimage, Equiv.apply_symm_apply] using hmem

/-- The complete type attached to an actual orbit, preserving its tuple representative. -/
def orbitType (n : ℕ) : OrbitClass L M n → T.CompleteType (Fin n) :=
  Quotient.lift (fun a => T.typeOf a) (fun a b h => sameOrbit_typeOf a b h)

/-- Finitely many orbits imply finitely many realized types, without any homogeneity hypothesis. -/
theorem finite_realized_types_of_orbits {n : ℕ} [Finite (OrbitClass L M n)] :
    (Set.range (fun a : Fin n → M => T.typeOf a)).Finite := by
  have hr : Set.range (fun a : Fin n → M => T.typeOf a) =
      Set.range (orbitType (T := T) (M := M) n) := by
    ext p
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨Quotient.mk _ a, rfl⟩
    · rintro ⟨c, hc⟩
      induction c using Quotient.inductionOn with | h a =>
        exact ⟨a, hc⟩
  rw [hr]
  exact Set.finite_range _

/-- Completeness rules out an extra omitted type when the list of realized types is finite. -/
theorem finite_realized_types_exhaust (hT : T.IsComplete) {n : ℕ}
    (hf : (Set.range (fun a : Fin n → M => T.typeOf a)).Finite) :
    Finite (T.CompleteType (Fin n)) ∧
      Function.Surjective (fun a : Fin n → M => T.typeOf a) := by
  classical
  let R := Set.range (fun a : Fin n → M => T.typeOf a)
  have hall : ∀ p : T.CompleteType (Fin n), p ∈ R := by
    intro p
    by_contra hp
    have hs : ∀ q : R, ∃ φ ∈ formulas p, φ.not ∈ formulas q.val := by
      intro q
      exact IsolatedTypes.separates p q.val (fun h => hp (h.symm ▸ q.prop))
    choose φ hpφ hqφ using hs
    let Γ : Finset (L.Formula (Fin n)) := hf.toFinset.attach.image
      (fun q => φ ⟨q.val, by simpa only [Set.Finite.mem_toFinset] using q.prop⟩)
    have hΓ : (↑Γ : Set _) ⊆ formulas p := by
      intro ψ hψ
      obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hψ
      exact hpφ _
    obtain ⟨a, ha⟩ := OmittingTypes.complete_type_finitely_realized (M := M) hT p Γ hΓ
    let q : R := ⟨T.typeOf a, Set.mem_range_self a⟩
    have hmem : φ q ∈ Γ := by
      apply Finset.mem_image.mpr
      refine ⟨⟨q.val, ?_⟩, Finset.mem_attach _ _, ?_⟩
      · exact hf.mem_toFinset.mpr q.prop
      · rfl
    have hpos := ha _ hmem
    have hneg : (φ q).not.Realize a := Theory.CompleteType.formula_mem_typeOf.mp (hqφ q)
    exact Formula.realize_not.mp hneg hpos
  have hsur : Function.Surjective (fun a : Fin n → M => T.typeOf a) := hall
  have hfinite : Finite (T.CompleteType (Fin n)) := by
    let := hf.to_subtype
    exact Finite.of_surjective (fun q : R => q.val) (fun p => ⟨⟨p, hall p⟩, rfl⟩)
  exact ⟨hfinite, hsur⟩

end Lemmatheca.ModelTheory.CountableCategoricity
