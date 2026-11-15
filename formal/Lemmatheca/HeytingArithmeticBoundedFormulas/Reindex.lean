import Lemmatheca.HeytingArithmeticBoundedFormulas.Syntax
import Lemmatheca.HeytingArithmeticStrongInduction.Certificates
import Mathlib.Logic.Equiv.Fin.Basic

/-! Exact finite-name adapters for the already proved original HA induction operation. -/
namespace Lemmatheca.ProofTheory.HeytingArithmetic.Bounded
open _root_.FirstOrder _root_.FirstOrder.Language
open Lemmatheca.ProofTheory.FirstOrder.BoundedFormula
open Lemmatheca.ProofTheory.HeytingArithmetic.StrongInduction

/-- Keep the old positions, then put the new input at the last position. -/
def extendedNumbering (k : ℕ) : (Fin k ⊕ Unit) ≃ Fin (k + 1) :=
  (Equiv.sumCongr (Equiv.refl (Fin k)) (Equiv.ofUnique Unit (Fin 1))).trans finSumFinEquiv

theorem extendedNumbering_old (k : ℕ) (i : Fin k) :
    extendedNumbering k (.inl i) = i.castSucc := by
  apply Fin.ext
  simp [extendedNumbering]

theorem extendedNumbering_new (k : ℕ) :
    extendedNumbering k (.inr ()) = Fin.last k := by
  apply Fin.ext
  simp [extendedNumbering, Equiv.ofUnique]

theorem formula_reindex_roundtrip {α β : Type} (e : α ≃ β) (A : Formula α) :
    (A.rename e).rename e.symm = A := by
  rw [rename_comp]
  have hi : (e.symm ∘ e : α → α) = id := by
    funext x
    exact e.symm_apply_apply x
  rw [hi, rename_id]

noncomputable section
local instance habfReindexEq {δ : Type} : DecidableEq (Formula δ) := Classical.decEq _

/-- Rename body, bound and context together; use only the original Fin-k induction. -/
def searchByEquiv {α : Type} {k : ℕ} (e : α ≃ Fin k)
    (A : Formula (α ⊕ Unit)) (t : LA.Term α) {Γ : Context α}
    (p : Certificate false Γ (predicateDecision A)) :
    Certificate false Γ (finiteSearch A t) := by
  let A_e := parameterRename A (e : α → Fin k)
  let Γ_e : Context (Fin k) := Γ.image (fun B => B.rename (e : α → Fin k))
  have p_e : Certificate false Γ_e (predicateDecision A_e) := by
    simpa only [Γ_e, A_e, predicateDecision_rename] using p.universeRename (e : α → Fin k)
  have q := boundedSearchAt A_e p_e (t.relabel (e : α → Fin k))
  have r := q.universeRename (e.symm : Fin k → α)
  have hi : (e.symm ∘ e : α → α) = id := by
    funext x
    exact e.symm_apply_apply x
  have hc : Γ_e.image (fun B => B.rename (e.symm : Fin k → α)) = Γ := by
    simp only [Γ_e, Finset.image_image, Function.comp_def, formula_reindex_roundtrip,
      Finset.image_id']
  have ha : parameterRename A_e (e.symm : Fin k → α) = A := by
    dsimp only [A_e]
    rw [parameterRename_comp, hi, parameterRename_id]
  have ht : (t.relabel (e : α → Fin k)).relabel (e.symm : Fin k → α) = t := by
    rw [Term.relabel_relabel, hi, Term.relabel_id]
  simpa only [finiteSearch_rename, ha, ht, hc] using r

end
end Lemmatheca.ProofTheory.HeytingArithmetic.Bounded
