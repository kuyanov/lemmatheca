import Lemmatheca.MathematicalLogic.PreservationBasic
import Lemmatheca.MathematicalLogic.BasicStructures

/-! A relative order example separating the ambient theory from all orders. -/
namespace Lemmatheca.Entry.PreservationConverses
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic.FirstOrderSyntax
open Lemmatheca.MathematicalLogic.FirstOrderSemantics

/-- The free element has a larger element in the strict-order relation. -/
def above : binaryRelLanguage.Formula (Fin 1) :=
  (Relations.boundedFormula₂ BinaryRelationSymbol.rel (.var (.inl 0)) (.var (.inr 0))).ex

/-- In orders without a greatest element, the formula is equivalent to truth. -/
theorem above_equivalent_truth {M : Type*} (r : M → M → Prop)
    (h : ∀ x, ∃ y, r x y) :
    let := binaryRelStructure M r
    ∀ a : Fin 1 → M, above.Realize a ↔ (⊤ : binaryRelLanguage.Formula (Fin 1)).Realize a := by
  dsimp only
  intro a
  simp only [above, Formula.Realize, BoundedFormula.realize_ex,
    BoundedFormula.realize_top]
  change (∃ y, r (a 0) y) ↔ True
  exact iff_true_intro (h (a 0))

/-- Throughout all strict linear orders there is no equivalent universal formula. -/
theorem above_not_universal :
    ¬ ∃ ψ : binaryRelLanguage.Formula (Fin 1), ψ.IsUniversal ∧
      ∀ (M : Type) (r : M → M → Prop), IsStrictTotalOrder M r →
        let := binaryRelStructure M r
        ∀ a : Fin 1 → M, ψ.Realize a ↔ above.Realize a := by
  rintro ⟨ψ, hψ, heq⟩
  let := binaryRelStructure (Fin 1) (fun a b => a < b)
  let := binaryRelStructure (Fin 2) (fun a b => a < b)
  let f : Fin 1 ↪[binaryRelLanguage] Fin 2 :=
    { toFun := fun _ => 0
      inj' := fun _ _ _ => Subsingleton.elim _ _
      map_fun' := by intro n g; exact g.elim
      map_rel' := by
        intro n R x
        cases R
        change ((0 : Fin 2) < 0) ↔ x 0 < x 1
        have hx : x 0 = x 1 := Subsingleton.elim _ _
        simp [hx] }
  have hN : ψ.Realize (fun _ : Fin 1 => (0 : Fin 2)) := by
    apply (heq (Fin 2) (· < ·) inferInstance (fun _ => 0)).mpr
    simp only [above, Formula.Realize, BoundedFormula.realize_ex]
    change ∃ y : Fin 2, (0 : Fin 2) < y
    exact ⟨1, by decide⟩
  have hM : ψ.Realize (fun _ : Fin 1 => (0 : Fin 1)) := by
    apply hψ.realize_embedding f
    convert hN using 1
    apply Iff.of_eq
    congr 1
    ext i
    exact Fin.elim0 i
  have ha := (heq (Fin 1) (· < ·) inferInstance (fun _ => 0)).mp hM
  simp only [above, Formula.Realize, BoundedFormula.realize_ex] at ha
  change ∃ y : Fin 1, (0 : Fin 1) < y at ha
  obtain ⟨y, hy⟩ := ha
  have hy0 : y = 0 := Subsingleton.elim _ _
  simp [hy0] at hy

end Lemmatheca.Entry.PreservationConverses
