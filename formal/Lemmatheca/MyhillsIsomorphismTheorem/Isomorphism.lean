import Lemmatheca.MyhillsIsomorphismTheorem.Matching

namespace Lemmatheca.ComputabilityTheory.Myhill

def ComputablePermutation (h : ℕ → ℕ) : Prop := Computable h ∧ Function.Bijective h

def ComputablyIsomorphic (A B : Set ℕ) : Prop :=
  ∃ h : ℕ → ℕ, ComputablePermutation h ∧ ∀ x, x ∈ A ↔ h x ∈ B

noncomputable def inverseSearch (h : ℕ → ℕ) (hs : Function.Surjective h)
    (y : ℕ) : ℕ := Nat.find (hs y)

theorem inverse_search (h : ℕ → ℕ) (hc : Computable h) (hb : Function.Bijective h) :
    Computable (inverseSearch h hb.2) ∧
      Function.LeftInverse (inverseSearch h hb.2) h ∧
      Function.RightInverse (inverseSearch h hb.2) h ∧
      ∀ y, h (inverseSearch h hb.2 y) = y ∧
        ∀ x < inverseSearch h hb.2 y, h x ≠ y := by
  have hp : ComputablePred (fun p : ℕ × ℕ => h p.2 = p.1) := by
    apply Computable.computablePred
    exact Primrec.eq.decide.to_comp.comp (hc.comp Computable.snd) Computable.fst
  have hj : Computable (inverseSearch h hb.2) := Computable.find hp hb.2
  have hr : Function.RightInverse (inverseSearch h hb.2) h := by
    intro y
    exact Nat.find_spec (hb.2 y)
  have hl : Function.LeftInverse (inverseSearch h hb.2) h := by
    intro x
    exact hb.1 (hr (h x))
  refine ⟨hj, hl, hr, ?_⟩
  intro y
  exact ⟨hr y, fun x hx => Nat.find_min (hb.2 y) hx⟩

theorem myhill (A B : Set ℕ) :
    OneOneEquiv A B ↔ ComputablyIsomorphic A B := by
  constructor
  · rintro ⟨⟨f, hfc, hfi, hf⟩, ⟨g, hgc, hgi, hg⟩⟩
    have hl := labelled_bijection (fun x => x ∈ A) (fun y => y ∈ B) f g
      hfc hgc hfi hgi (fun x => propext (hf x)) (fun y => propext (hg y))
    refine ⟨forward f g, ⟨hl.1, (inverse_identities f g hfi hgi).2.2⟩, ?_⟩
    intro x
    exact Iff.of_eq (hl.2.2.2.2 x)
  · rintro ⟨h, ⟨hc, hb⟩, he⟩
    have hk := inverse_search h hc hb
    refine ⟨⟨h, hc, hb.1, he⟩,
      ⟨inverseSearch h hb.2, hk.1, hk.2.2.1.injective, ?_⟩⟩
    intro y
    have hm := he (inverseSearch h hb.2 y)
    rw [hk.2.2.1 y] at hm
    exact hm.symm

end Lemmatheca.ComputabilityTheory.Myhill
