import Lemmatheca.MathematicalLogic.Compactness

/-! The zero-and-successor example for unnamed elements. -/
namespace Lemmatheca.Entry.LogicalCompactness
open FirstOrder FirstOrder.Language
noncomputable section

inductive SuccessorFunction : ℕ → Type
  | zero : SuccessorFunction 0
  | succ : SuccessorFunction 1

def successorLanguage : Language := ⟨SuccessorFunction, fun _ => Empty⟩

private instance countableFunctions : Countable (Σ n, SuccessorFunction n) := by
  refine Function.Injective.countable (f := fun p : Σ n, SuccessorFunction n =>
    match p with | ⟨_, .zero⟩ => false | ⟨_, .succ⟩ => true) ?_
  intro a b h
  obtain ⟨_, a⟩ := a
  obtain ⟨_, b⟩ := b
  cases a <;> cases b <;> simp_all

instance countableSymbols : Countable successorLanguage.Symbols := by
  change Countable ((Σ n, SuccessorFunction n) ⊕ (Σ _ : ℕ, Empty))
  infer_instance

instance natStructure : successorLanguage.Structure ℕ where
  funMap f ts := match f with
    | .zero => 0
    | .succ => ts 0 + 1
  RelMap r _ := r.elim

def numeral : ℕ → successorLanguage.Term Empty
  | 0 => .func .zero Fin.elim0
  | n + 1 => .func .succ (fun _ => numeral n)

private theorem numeral_value (n : ℕ) : (numeral n).realize Empty.elim = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (numeral n).realize Empty.elim + 1 = n + 1
    rw [ih]

theorem closed_terms_are_numerals (t : successorLanguage.Term Empty) :
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
    ∃ N : Theory.ModelType.{0, 0, 0} (successorLanguage.completeTheory ℕ),
      ∃ x : N, ∀ t : successorLanguage.Term Empty, x ≠ t.realize Empty.elim := by
  exact Lemmatheca.MathematicalLogic.Compactness.exists_unnamed_element
    (successorLanguage.completeTheory ℕ) ℕ

end
end Lemmatheca.Entry.LogicalCompactness
