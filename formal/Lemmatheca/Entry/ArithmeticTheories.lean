import Lemmatheca.MathematicalLogic.ArithmeticTheories
import Mathlib.Data.ENat.Monoid

/-! An illustrative one-point extension showing Robinson arithmetic's weakness. -/
namespace Lemmatheca.Entry.ArithmeticTheories
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic.ArithmeticTheories
open Lemmatheca.MathematicalLogic.FirstOrderProofs

instance infinityStructure : language.Structure ℕ∞ where
  funMap f ts := match f with
    | .zero => 0
    | .succ => ts 0 + 1
    | .add => ts 0 + ts 1
    | .mul => ts 0 * ts 1
  RelMap r _ := r.elim

theorem infinity_models_Q : ℕ∞ ⊨ Q := by
  rw [model_Q_iff]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a
    change a + 1 ≠ 0
    simp
  · intro a b h
    change a + 1 = b + 1 at h
    apply ENat.add_right_injective_of_ne_top (n := 1) (by simp)
    simpa only [add_comm] using h
  · intro a ha
    induction a using ENat.recTopCoe with
    | top =>
      refine ⟨⊤, ?_⟩
      change (⊤ : ℕ∞) = ⊤ + 1
      simp
    | coe n =>
      have hn : n ≠ 0 := by
        intro h
        subst n
        exact ha rfl
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
      exact ⟨(k : ℕ∞), rfl⟩
  · intro a
    exact add_zero a
  · intro a b
    exact (add_assoc a b 1).symm
  · intro a
    exact mul_zero a
  · intro a b
    exact mul_add_one a b

theorem infinity_successor_fixed : succValue ℕ∞ ⊤ = ⊤ := by
  change (⊤ : ℕ∞) + 1 = ⊤
  simp

theorem Q_not_derives_no_fixed_point : ¬ Derives Q noFixedPointSentence := by
  intro h
  have hempty (θ : language.Sentence) :
      (ℕ∞ ⊨ θ) ↔ Formula.Realize θ (Empty.elim : Empty → ℕ∞) := by
    rw [Sentence.Realize, iff_eq_eq]
    congr 1
    exact Subsingleton.elim _ _
  have htruth : ℕ∞ ⊨ noFixedPointSentence :=
    (hempty _).mpr (derives_sound h (Empty.elim : Empty → ℕ∞)
      (fun φ hφ => (hempty φ).mp (infinity_models_Q.realize_of_mem φ hφ)))
  rw [noFixedPointSentence, realize_close] at htruth
  have htop := htruth (fun _ => ⊤)
  change succValue ℕ∞ ⊤ ≠ ⊤ at htop
  exact htop infinity_successor_fixed

end Lemmatheca.Entry.ArithmeticTheories
