import Lemmatheca.SaturatedModels.Saturation
import Lemmatheca.DefinableAndAlgebraicClosure.Closures

/-! Actual parameter-fixing automorphisms and their tuple and point orbits. -/
namespace Lemmatheca.ModelTheory.TypesAndSymmetry

open FirstOrder FirstOrder.Language

universe u v w
variable {L : Language.{u,v}} {M : Type w} [L.Structure M]

def AutOver (L : Language.{u,v}) {M : Type w} [L.Structure M] (A : Set M) :=
  {g : M ≃[L] M // Definability.Fixes g A}

def tupleOrbit (A : Set M) {n : ℕ} (a : Fin n → M) : Set (Fin n → M) :=
  {b | ∃ g : AutOver L A, ∀ i, g.val (a i) = b i}

def pointOrbit (A : Set M) (a : M) : Set M :=
  {b | ∃ g : AutOver L A, g.val a = b}

theorem orbit_equivalence (A : Set M) (n : ℕ) :
    Equivalence (fun a b : Fin n → M => b ∈ tupleOrbit (L := L) A a) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a
    exact ⟨⟨Language.Equiv.refl L M, fun _ _ => rfl⟩, fun _ => rfl⟩
  · rintro a b ⟨⟨g, hg⟩, hab⟩
    exact ⟨⟨g.symm, Definability.fixes_symm g hg⟩, fun i => by
      rw [← hab i]; exact g.symm_apply_apply _⟩
  · rintro a b c ⟨⟨g, hg⟩, hab⟩ ⟨⟨h, hh⟩, hbc⟩
    refine ⟨⟨h.comp g, fun x hx => ?_⟩, fun i => ?_⟩
    · change h (g x) = x
      rw [hg x hx, hh x hx]
    · change h (g (a i)) = c i
      rw [hab, hbc]

theorem point_mem_own_orbit (A : Set M) (a : M) : a ∈ pointOrbit (L := L) A a := by
  exact ⟨⟨Language.Equiv.refl L M, fun _ _ => rfl⟩, rfl⟩

theorem empty_tuple_orbit (A : Set M) (a : Fin 0 → M) :
    tupleOrbit (L := L) A a = Set.univ := by
  apply Set.eq_univ_of_forall
  intro b
  exact ⟨⟨Language.Equiv.refl L M, fun _ _ => rfl⟩, fun i => Fin.elim0 i⟩

variable [Nonempty M]

theorem orbit_preserves_type (A : Set M) {n : ℕ} (a b : Fin n → M)
    (h : b ∈ tupleOrbit (L := L) A a) :
    (L[[A]].completeTheory M).typeOf a = (L[[A]].completeTheory M).typeOf b := by
  obtain ⟨⟨g, hg⟩, hab⟩ := h
  apply SetLike.ext
  intro γ
  change γ ∈ ((L[[A]].completeTheory M).typeOf a).toTheory ↔
    γ ∈ ((L[[A]].completeTheory M).typeOf b).toTheory
  let φ := Formula.equivSentence.symm γ
  have hD : A.Definable L (Set.ofPred φ.Realize) := ⟨φ, rfl⟩
  have hφ : φ.Realize a ↔ φ.Realize b := by
    have h := Definability.definable_invariant hD g hg a
    have heq : g ∘ a = b := funext hab
    simpa only [Set.mem_ofPred_eq, heq] using h
  have hm : φ ∈ Types.formulas ((L[[A]].completeTheory M).typeOf a) ↔
      φ ∈ Types.formulas ((L[[A]].completeTheory M).typeOf b) :=
    Theory.CompleteType.formula_mem_typeOf.trans
      (hφ.trans Theory.CompleteType.formula_mem_typeOf.symm)
  simpa only [φ, Types.formulas, Set.mem_preimage, Equiv.apply_symm_apply] using hm

omit [Nonempty M] in
theorem definable_orbit_invariant (A : Set M) {n : ℕ} (D : Set (Fin n → M))
    (hD : A.Definable L D) (g : AutOver L A) : Definability.Invariant g.val D := by
  exact Definability.definable_invariant hD g.val g.property

theorem type_iff_tuple_orbit [Countable M] (hM : Saturation.OmegaSaturated L M)
    (A : Set M) (hA : A.Finite) {n : ℕ} (a b : Fin n → M) :
    (L[[A]].completeTheory M).typeOf a = (L[[A]].completeTheory M).typeOf b ↔
      b ∈ tupleOrbit (L := L) A a := by
  constructor
  · intro h
    obtain ⟨g, hg, hab⟩ := Saturation.homogeneity hM A hA a b h
    exact ⟨⟨g, hg⟩, hab⟩
  · exact orbit_preserves_type A a b

theorem type_iff_point_orbit [Countable M] (hM : Saturation.OmegaSaturated L M)
    (A : Set M) (hA : A.Finite) (a b : M) :
    (L[[A]].completeTheory M).typeOf (fun _ : Fin 1 => a) =
      (L[[A]].completeTheory M).typeOf (fun _ : Fin 1 => b) ↔
      b ∈ pointOrbit (L := L) A a := by
  rw [type_iff_tuple_orbit hM A hA]
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨g, hg 0⟩
  · rintro ⟨g, hg⟩
    exact ⟨g, fun _ => hg⟩

end Lemmatheca.ModelTheory.TypesAndSymmetry
