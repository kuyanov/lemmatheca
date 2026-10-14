import Lemmatheca.MathematicalLogic.Compactness
import Lemmatheca.MathematicalLogic.BasicStructures

/-! The zero-and-successor example for unnamed elements. -/
namespace Lemmatheca.Entry.LogicalCompactness
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic.BasicStructures
noncomputable section

theorem closed_terms_are_numerals (t : naturalSuccessorLanguage.Term Empty) :
    ∃ n : ℕ, t = numeral n ∧ t.realize Empty.elim = n := by
  induction t with
  | var e => cases e
  | @func k f ts ih =>
    cases f with
    | zero =>
      have hts : ts = Fin.elim0 := by funext i; exact Fin.elim0 i
      subst ts
      exact ⟨0, rfl, rfl⟩
    | succ =>
      obtain ⟨n, hn, _⟩ := ih 0
      have hts : ts = fun _ => numeral n := by
        funext i
        have hi : i = 0 := Fin.eq_zero i
        simpa [hi] using hn
      rw [hts]
      exact ⟨n + 1, rfl, numeral_value (n + 1)⟩

theorem natural_number_theory_has_unnamed_model :
    ∃ N : Theory.ModelType.{0, 0, 0} (naturalSuccessorLanguage.completeTheory ℕ),
      ∃ x : N, ∀ t : naturalSuccessorLanguage.Term Empty, x ≠ t.realize Empty.elim := by
  exact Lemmatheca.MathematicalLogic.Compactness.exists_unnamed_element
    (naturalSuccessorLanguage.completeTheory ℕ) ℕ

end
end Lemmatheca.Entry.LogicalCompactness
