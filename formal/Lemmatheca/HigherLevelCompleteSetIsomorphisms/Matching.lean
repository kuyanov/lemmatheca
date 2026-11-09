import Lemmatheca.HigherLevelCompleteSetIsomorphisms.Escape
import Lemmatheca.MyhillsIsomorphismTheorem.Isomorphism

/-! The actual padding injections and the same Myhill forward and backward maps. -/
namespace Lemmatheca.ComputabilityTheory.HigherCompleteIsomorphism

open OraclePadding TuringJump Myhill

noncomputable section
set_option backward.isDefEq.respectTransparency false

def IsomorphismPair (S T : Set ℕ) (P Q : ℕ → ℕ) : Prop :=
  Computable P ∧ Computable Q ∧ Function.LeftInverse Q P ∧
    Function.RightInverse Q P ∧ ∀ x, x ∈ S ↔ P x ∈ T

theorem pair_iff_isomorphic (S T : Set ℕ) :
    (∃ P Q, IsomorphismPair S T P Q) ↔ ComputablyIsomorphic S T := by
  constructor
  · rintro ⟨P, Q, hcP, _hcQ, hl, hr, hmem⟩
    exact ⟨P, ⟨hcP, hl.injective, hr.surjective⟩, hmem⟩
  · rintro ⟨P, ⟨hcP, hbP⟩, hmem⟩
    have hi := inverse_search P hcP hbP
    exact ⟨P, inverseSearch P hbP.2, hcP, hi.1, hi.2.1, hi.2.2.1, hmem⟩

def paddedReduction (f : ℕ → ℕ) (x : ℕ) : ℕ := pad (f x) x

theorem padded_reduction_spec {A C : Set ℕ} {f : ℕ → ℕ} (hf : Computable f)
    (hred : ∀ x, x ∈ C ↔ f x ∈ haltsZero A) :
    Computable (paddedReduction f) ∧ Function.Injective (paddedReduction f) ∧
      ∀ x, x ∈ C ↔ paddedReduction f x ∈ haltsZero A := by
  refine ⟨pad_primitive.to_comp.comp hf Computable.id, ?_, ?_⟩
  · intro x y hxy
    exact (pad_injective hxy).2
  · intro x
    change x ∈ C ↔ (OracleProgramNumberings.phi A (pad (f x) x) 0).Dom
    rw [pad_eval]
    exact hred x

def forwardInjection (f : ℕ → ℕ) (x : ℕ) : ℕ := zeroToDiagonal (paddedReduction f x)

def backwardInjection (g N M : ℕ → ℕ) (y : ℕ) : ℕ :=
  replacement g N M (diagonalToZero y)

def permutation (f g N M : ℕ → ℕ) : ℕ → ℕ :=
  Myhill.forward (forwardInjection f) (backwardInjection g N M)

def inversePermutation (f g N M : ℕ → ℕ) : ℕ → ℕ :=
  Myhill.backward (forwardInjection f) (backwardInjection g N M)

theorem specified_isomorphism {A C : Set ℕ} {f g N M : ℕ → ℕ}
    (hf : Computable f) (hg : Computable g) (hN : Primrec N) (hM : Primrec M)
    (hfred : ∀ x, x ∈ C ↔ f x ∈ haltsZero A) (hgred : ReducesZero A g C)
    (hn : IsFirstSelector g N) (hm : IsSecondSelector g M) :
    IsomorphismPair C (jump A) (permutation f g N M) (inversePermutation f g N M) := by
  have hi₀ := padded_reduction_spec hf hfred
  have hb := replacement_spec hg hN hM hn hm
  have hbA := hb.2 A C hgred
  have hci : Computable (forwardInjection f) :=
    zeroToDiagonal_primitive.to_comp.comp hi₀.1
  have hbi : Function.Injective (forwardInjection f) :=
    zeroToDiagonal_injective.comp hi₀.2.1
  have hmi : ∀ x, x ∈ C ↔ forwardInjection f x ∈ jump A :=
    fun x => (hi₀.2.2 x).trans (zeroToDiagonal_membership A _)
  have hcj : Computable (backwardInjection g N M) :=
    hb.1.comp diagonalToZero_primitive.to_comp
  have hbj : Function.Injective (backwardInjection g N M) :=
    hbA.1.comp diagonalToZero_injective
  have hmj : ∀ y, y ∈ jump A ↔ backwardInjection g N M y ∈ C :=
    fun y => (diagonalToZero_membership A y).trans (hbA.2 _)
  have hp := labelled_bijection (fun x => x ∈ C) (fun y => y ∈ jump A)
    (forwardInjection f) (backwardInjection g N M) hci hcj hbi hbj
    (fun x => propext (hmi x)) (fun y => propext (hmj y))
  exact ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, fun x => Iff.of_eq (hp.2.2.2.2 x)⟩

theorem jump_oneone_equivalence (A C : Set ℕ) :
    ManyOneEquiv C (jump A) ↔ OneOneEquiv C (jump A) := by
  constructor
  · rintro ⟨⟨f, hfc, hfred⟩, ⟨g, hgc, hgred⟩⟩
    let f₀ : ℕ → ℕ := diagonalToZero ∘ f
    let g₀ : ℕ → ℕ := g ∘ zeroToDiagonal
    have hf₀ : Computable f₀ := diagonalToZero_primitive.to_comp.comp hfc
    have hg₀ : Computable g₀ := hgc.comp zeroToDiagonal_primitive.to_comp
    have hfred₀ : ∀ x, x ∈ C ↔ f₀ x ∈ haltsZero A :=
      fun x => (hfred x).trans (diagonalToZero_membership A _)
    have hgred₀ : ReducesZero A g₀ C :=
      fun x => (zeroToDiagonal_membership A x).trans (hgred _)
    obtain ⟨N, M, hN, hM, hn, hm⟩ := common_selectors hg₀
    have hi₀ := padded_reduction_spec hf₀ hfred₀
    have hb := replacement_spec hg₀ hN hM hn hm
    have hbA := hb.2 A C hgred₀
    refine ⟨⟨forwardInjection f₀, zeroToDiagonal_primitive.to_comp.comp hi₀.1,
      zeroToDiagonal_injective.comp hi₀.2.1, ?_⟩,
      ⟨backwardInjection g₀ N M, hb.1.comp diagonalToZero_primitive.to_comp,
        hbA.1.comp diagonalToZero_injective, ?_⟩⟩
    · intro x
      exact (hi₀.2.2 x).trans (zeroToDiagonal_membership A _)
    · intro y
      exact (diagonalToZero_membership A y).trans (hbA.2 _)
  · rintro ⟨⟨f, hfc, _hfi, hfred⟩, ⟨g, hgc, _hgi, hgred⟩⟩
    exact ⟨⟨f, hfc, hfred⟩, ⟨g, hgc, hgred⟩⟩

theorem jump_isomorphism_equivalence (A C : Set ℕ) :
    ManyOneEquiv C (jump A) ↔ ComputablyIsomorphic C (jump A) := by
  exact (jump_oneone_equivalence A C).trans (myhill C (jump A))

end
end Lemmatheca.ComputabilityTheory.HigherCompleteIsomorphism
