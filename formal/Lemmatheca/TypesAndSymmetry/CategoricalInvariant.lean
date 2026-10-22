import Lemmatheca.TypesAndSymmetry.Orbits
import Lemmatheca.CountableCategoricity.Categoricity

/-! Finite native automorphism orbits turn arbitrary invariant sets into finite definitions. -/
namespace Lemmatheca.ModelTheory.TypesAndSymmetry

open FirstOrder FirstOrder.Language

variable {L : Language.{0,0}} {T : L.Theory} {M : Type}
  [L.Structure M] [Nonempty M] [Countable M] [M ⊨ T] [Countable L.Symbols]

theorem categorical_definable_iff_invariant (hT : T.IsComplete)
    (hInf : ∃ N : T.ModelType.{0,0,0}, Infinite N)
    (hcat : (Cardinal.aleph0 : Cardinal.{0}).Categorical T)
    (n : ℕ) (D : Set (Fin n → M)) :
    (∅ : Set M).Definable L D ↔
      ∀ g : M ≃[L] M, Definability.Invariant g D  := by
  classical
  constructor
  · intro hD g
    exact Definability.definable_invariant hD g (fun _ h => h.elim)
  · intro hD
    let : Finite (CountableCategoricity.OrbitClass L M n) :=
      CountableCategoricity.categorical_oligomorphic (M := M) hT hInf hcat n
    let I := {c : CountableCategoricity.OrbitClass L M n //
      ∃ a : Fin n → M, a ∈ D ∧ Quotient.mk _ a = c}
    choose rep hrepD hrep using fun i : I => i.property
    have hd (i : I) : (∅ : Set M).Definable L
        {b : Fin n → M | CountableCategoricity.SameOrbit (L := L) (rep i) b} := by
      obtain ⟨θ, _, hθ⟩ := CountableCategoricity.orbit_isolator hT hInf hcat (rep i)
      exact Set.empty_definable_iff.mpr ⟨θ, Set.ext hθ⟩
    have heq : D = ⋃ i : I,
        {b : Fin n → M | CountableCategoricity.SameOrbit (L := L) (rep i) b} := by
      ext b
      constructor
      · intro hb
        let i : I := ⟨Quotient.mk _ b, ⟨b, hb, rfl⟩⟩
        exact Set.mem_iUnion.mpr ⟨i, Quotient.exact (hrep i)⟩
      · intro hb
        obtain ⟨i, g, hg⟩ := Set.mem_iUnion.mp hb
        have h := (hD g (rep i)).mp (hrepD i)
        have heq : g ∘ rep i = b := funext hg
        exact heq ▸ h
    rw [heq]
    exact Set.definable_iUnion_of_finite hd

end Lemmatheca.ModelTheory.TypesAndSymmetry
