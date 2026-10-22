import Lemmatheca.ExistentiallyClosedExtensions.Basics

/-! The bounded native limit used at a nonzero limit stage of the request pass. -/
namespace Lemmatheca.ModelTheory.ExistentiallyClosedExtensions
open FirstOrder FirstOrder.Language Cardinal
open Lemmatheca.ModelTheory
open InductiveTheories
universe u v w
variable {L : Language.{u, v}}

/-- Recoding a directed union keeps its canonical maps, compatibility and coverage. -/
theorem bounded_coded_directLimit (T : L.Theory) (hT : IsInductive.{u, v, w} T)
    (κ : Cardinal.{max u v w}) (hω : ℵ₀ ≤ κ)
    {I : Type (max u v w)} [Preorder I] [IsDirectedOrder I] [Nonempty I]
    (hI : #I ≤ κ) (G : I → Theory.ModelType.{u, v, max u v w} T)
    (hG : ∀ i, #(G i) ≤ κ)
    (f : ∀ i j, i ≤ j → G i ↪[L] G j)
    [DirectedSystem (fun i => G i) (fun i j h => f i j h)] :
    ∃ (C : CodedModel T κ)
      (e : FirstOrder.Language.DirectLimit (fun i => G i) f ≃[L] C.asModel),
      (∀ i j (hij : i ≤ j) (a : G i),
        e (DirectLimit.of L I (fun i => G i) f j (f i j hij a)) =
          e (DirectLimit.of L I (fun i => G i) f i a)) ∧
      (∀ c : C.asModel, ∃ (i : I) (a : G i), e (DirectLimit.of L I (fun i => G i) f i a) = c) := by
  classical
  let D := FirstOrder.Language.DirectLimit (fun i => G i) f
  let : Nonempty D := Nonempty.map (DirectLimit.of L I (fun i => G i) f
    (Classical.choice inferInstance)) inferInstance
  have haxi : HasUniversalExistentialAxiomatization T := by
    obtain ⟨h₁, h₂, h₃, _⟩ := inductive_characterization.{u, v, w} T
    exact h₃.mp (h₂.mp (h₁.mp hT))
  have hmodel : D ⊨ T := axiomatization_directed_union T haxi (fun i => G i) f
    (fun _ => inferInstance)
  let := hmodel
  have hsurj : Function.Surjective (fun x : Sigma (fun i => G i) =>
      DirectLimit.of L I (fun i => G i) f x.1 x.2) := by
    intro x
    obtain ⟨i, a, ha⟩ := DirectLimit.exists_of x
    exact ⟨⟨i, a⟩, ha⟩
  have hcard : #D ≤ κ := by
    apply (Cardinal.mk_le_of_surjective hsurj).trans
    rw [Cardinal.mk_sigma]
    calc
      Cardinal.sum (fun i => #(G i)) ≤ Cardinal.sum (fun _ : I => κ) :=
        Cardinal.sum_le_sum _ _ hG
      _ = #I * κ := Cardinal.sum_const' I κ
      _ ≤ κ := Cardinal.mul_le_of_le hω hI le_rfl
  obtain ⟨C, ⟨e⟩⟩ := code_model T κ (Theory.ModelType.of T D) hcard
  refine ⟨C, e, ?_, ?_⟩
  · intro i j hij a
    exact congrArg e (DirectLimit.of_f (f := f) (i := i) (j := j) (hij := hij) (x := a))
  · intro c
    obtain ⟨i, a, ha⟩ := DirectLimit.exists_of (e.symm c)
    exact ⟨i, a, (congrArg e ha).trans (e.apply_symm_apply c)⟩

end Lemmatheca.ModelTheory.ExistentiallyClosedExtensions
