import Lemmatheca.MathematicalLogic.ArithmeticFormulaSubstitution

/-! Bounded quantification over a fixed finite tuple in the shared syntax. -/
namespace Lemmatheca.MathematicalLogic.ArithmeticRepresentability
open FirstOrder FirstOrder.Language
open ArithmeticTheories
noncomputable section
universe u

def boundedTupleEx {α : Type} (t : language.Term α) :
    (k : ℕ) → language.Formula (α ⊕ Fin k) → language.Formula α
  | 0, φ => φ.relabel (Sum.elim id Fin.elim0)
  | k + 1, φ => boundedEx t
      (boundedTupleEx (t.relabel Sum.inl) k
        (φ.relabel (Sum.elim (fun a => .inl (.inl a))
          (Fin.cases (.inl (.inr ())) (fun j => .inr j)))))

theorem boundedTupleEx_bounded {α : Type} (t : language.Term α) (k : ℕ)
    {φ : language.Formula (α ⊕ Fin k)} (hφ : DeltaZero φ) :
    DeltaZero (boundedTupleEx t k φ) := by
  induction k generalizing α with
  | zero => exact hφ.relabel _
  | succ k ih => exact .ex t (ih _ (hφ.relabel _))

theorem realize_boundedTupleEx {α : Type} {M : Type u} [language.Structure M]
    (t : language.Term α) (k : ℕ) (φ : language.Formula (α ⊕ Fin k)) (v : α → M) :
    (boundedTupleEx t k φ).Realize v ↔
      ∃ w : Fin k → M, (∀ j, leValue M (w j) (t.realize v)) ∧
        φ.Realize (Sum.elim v w) := by
  induction k generalizing α with
  | zero =>
    simp only [boundedTupleEx, Formula.realize_relabel]
    constructor
    · intro h
      refine ⟨Fin.elim0, fun j => j.elim0, ?_⟩
      convert h using 1
      funext x
      cases x with
      | inl x => rfl
      | inr j => exact j.elim0
    · rintro ⟨w, _, hw⟩
      convert hw using 1
      funext x
      cases x with
      | inl x => rfl
      | inr j => exact j.elim0
  | succ k ih =>
    rw [boundedTupleEx, realize_boundedEx]
    simp only [ih, Term.realize_relabel, Function.comp_def, extend, Sum.elim_inl,
      Formula.realize_relabel]
    constructor
    · rintro ⟨a, ha, w, hw, hφ⟩
      refine ⟨Fin.cons a w, ?_, ?_⟩
      · intro j
        refine Fin.cases ha (fun j => ?_) j
        exact hw j
      · convert hφ using 1
        funext x
        cases x with
        | inl x => rfl
        | inr j => refine Fin.cases rfl (fun j => rfl) j
    · rintro ⟨w, hw, hφ⟩
      refine ⟨w 0, hw 0, fun j => w j.succ, fun j => hw j.succ, ?_⟩
      convert hφ using 1
      funext x
      cases x with
      | inl x => rfl
      | inr j => refine Fin.cases rfl (fun j => rfl) j

def boundedTupleAll {α : Type} (t : language.Term α) (k : ℕ)
    (φ : language.Formula (α ⊕ Fin k)) : language.Formula α :=
  (boundedTupleEx t k φ.not).not

theorem realize_boundedTupleAll {α : Type} {M : Type u} [language.Structure M]
    (t : language.Term α) (k : ℕ) (φ : language.Formula (α ⊕ Fin k)) (v : α → M) :
    (boundedTupleAll t k φ).Realize v ↔
      ∀ w : Fin k → M, (∀ j, leValue M (w j) (t.realize v)) →
        φ.Realize (Sum.elim v w) := by
  classical
  rw [boundedTupleAll, Formula.realize_not, realize_boundedTupleEx]
  simp only [Formula.realize_not]
  constructor
  · intro h w hw
    by_contra hn
    exact h ⟨w, hw, hn⟩
  · rintro h ⟨w, hw, hn⟩
    exact hn (h w hw)

end
end Lemmatheca.MathematicalLogic.ArithmeticRepresentability
