import Lemmatheca.MathematicalLogic.QuantifierElimination
import Mathlib.ModelTheory.Definability

/-! Endpoint support for the explicit quantifier-free definitions of order cells. -/
namespace Lemmatheca.MathematicalLogic.QuantifierElimination

open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic.FirstOrderSyntax
open Lemmatheca.MathematicalLogic.FirstOrderSemantics

universe u

private theorem freeVarFinset_sup {L : Language} {M : Type u} [DecidableEq M]
    {n : ℕ} (φ ψ : L.BoundedFormula M n) :
    (φ ⊔ ψ).freeVarFinset = φ.freeVarFinset ∪ ψ.freeVarFinset := by
  change (φ.not.imp ψ).freeVarFinset = _
  simp [BoundedFormula.freeVarFinset]

private theorem freeVarFinset_inf {L : Language} {M : Type u} [DecidableEq M]
    {n : ℕ} (φ ψ : L.BoundedFormula M n) :
    (φ ⊓ ψ).freeVarFinset = φ.freeVarFinset ∪ ψ.freeVarFinset := by
  change (φ.imp ψ.not).not.freeVarFinset = _
  simp [BoundedFormula.freeVarFinset]

/-- A cell's defining formula uses only its point or finite endpoint parameters. -/
theorem Cell.toBoundedFormula_support {M : Type u} [DecidableEq M]
    (c : Cell M) (A : Set M) (h : c.Supported A) :
    ∀ a ∈ c.toBoundedFormula.freeVarFinset, a ∈ A := by
  cases c with
  | empty => simp [Cell.toBoundedFormula]
  | point b => simpa [Cell.toBoundedFormula, Cell.Supported, Term.varFinsetLeft] using h
  | interval l r =>
    cases l <;> cases r <;>
      simp_all [Cell.toBoundedFormula, Cell.Supported, freeVarFinset_inf, Term.varFinsetLeft,
        BoundedFormula.freeVarFinset, Fin.univ_succ]

/-- Every finite cell union has a quantifier-free definition using only a specified
set of parameters containing all its points and finite endpoints. -/
theorem finite_cell_union_definable_supported {M : Type u} [LT M] [DecidableEq M]
    (s : Finset (Cell M)) (A : Set M) (hs : ∀ c ∈ s, c.Supported A) :
    let : binaryRelLanguage.Structure M := binaryRelStructure M (fun a b => a < b)
    ∃ ψ : binaryRelLanguage.BoundedFormula M 1,
      ψ.IsQF ∧ (∀ a ∈ ψ.freeVarFinset, a ∈ A) ∧
      ∀ x : M, ψ.Realize id ![x] ↔ ∃ c ∈ s, x ∈ c.realize := by
  classical
  let : binaryRelLanguage.Structure M := binaryRelStructure M (fun a b => a < b)
  have hlist (l : List (Cell M)) (hl : ∀ c ∈ l, c.Supported A) :
      ∃ ψ : binaryRelLanguage.BoundedFormula M 1,
        ψ.IsQF ∧ (∀ a ∈ ψ.freeVarFinset, a ∈ A) ∧
        ∀ x : M, ψ.Realize id ![x] ↔ ∃ c ∈ l, x ∈ c.realize := by
    induction l with
    | nil => exact ⟨⊥, BoundedFormula.isQF_bot, by simp, fun x => by simp⟩
    | cons c l ih =>
      obtain ⟨ψ, hψ, hsψ, hψreal⟩ := ih (fun c hc => hl c (by simp [hc]))
      refine ⟨c.toBoundedFormula ⊔ ψ, c.toBoundedFormula_isQF.sup hψ, ?_, ?_⟩
      · intro a ha
        have hsc := c.toBoundedFormula_support A (hl c (by simp))
        rw [freeVarFinset_sup, Finset.mem_union] at ha
        exact ha.elim (hsc a) (hsψ a)
      · intro x
        simp only [BoundedFormula.realize_sup, c.toBoundedFormula_realize x, hψreal x,
          List.mem_cons, exists_eq_or_imp]
  obtain ⟨ψ, hψ, hsψ, hψreal⟩ := hlist s.toList (fun c hc => hs c (Finset.mem_toList.mp hc))
  exact ⟨ψ, hψ, hsψ, fun x => by simpa only [Finset.mem_toList] using hψreal x⟩

/-- The same converse expressed with the shared corpus predicate of definability
with parameters from the specified set. -/
theorem finite_cell_union_definable₁ {M : Type u} [LT M] [DecidableEq M]
    (s : Finset (Cell M)) (A : Set M) (hs : ∀ c ∈ s, c.Supported A) :
    let : binaryRelLanguage.Structure M := binaryRelStructure M (fun a b => a < b)
    A.Definable₁ binaryRelLanguage {x | ∃ c ∈ s, x ∈ c.realize} := by
  classical
  let : binaryRelLanguage.Structure M := binaryRelStructure M (fun a b => a < b)
  obtain ⟨ψ, _hψ, hsψ, hψreal⟩ := finite_cell_union_definable_supported s A hs
  let f : ψ.freeVarFinset → A := fun a => ⟨a, hsψ a a.2⟩
  let ψA := ψ.restrictFreeVar f
  apply Set.definable_iff_exists_formula_sum.mpr
  refine ⟨ψA.toFormula, ?_⟩
  ext xs
  change (∃ c ∈ s, xs 0 ∈ c.realize) ↔ ψA.toFormula.Realize (Sum.elim Subtype.val xs)
  rw [BoundedFormula.realize_toFormula]
  change (∃ c ∈ s, xs 0 ∈ c.realize) ↔ ψA.Realize Subtype.val xs
  rw [BoundedFormula.realize_restrictFreeVar (φ := ψ) (f := f) id (fun _ => rfl)]
  have hxs : xs = ![xs 0] := by funext i; have hi : i = 0 := Subsingleton.elim _ _; subst i; rfl
  rw [hxs]
  exact (hψreal (xs 0)).symm

end Lemmatheca.MathematicalLogic.QuantifierElimination
