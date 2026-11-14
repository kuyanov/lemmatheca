import Lemmatheca.EqualityFreeIntuitionisticFirstOrderSequents.Public
import Lemmatheca.IntuitionisticFirstOrderDeduction.Examples

/-! The quantified witness transport and the two explicit boundary examples. -/
namespace Lemmatheca.Entry.EqualityFreeIntuitionisticFirstOrderSequents
open _root_.FirstOrder _root_.FirstOrder.Language
open Lemmatheca.ProofTheory.IntuitionisticFirstOrder
abbrev Formula := Lemmatheca.ProofTheory.FirstOrder.Formula
universe u v w
variable {L : Language.{u,v}} {α : Type w}
noncomputable section
local instance ifoqExamplesFormulaEq {δ : Type w} : DecidableEq (Formula L δ) :=
  Classical.decEq _

/-- A cut-free witness transport, for arbitrary pure bodies and free parameters. -/
def quantifiedTransport (P Q : BF L α 1) (hP : P.EqualityFree) (hQ : Q.EqualityFree) :
    RawProof L ({(.all (.impl P Q)), (.ex P)} : Context L α) (.ex Q) := by
  refine ⟨?_, ?_, hQ⟩
  · let Γ : Context L α := {(.all (.impl P Q)), (.ex P)}
    apply CoreProof.exLeft (B := P) (by simp)
    let Δ : Context L (α ⊕ Fin 1) := insert P.toFormula (liftContext Γ)
    change CoreProof L Δ ((.ex Q : Formula L α).rename Sum.inl)
    have hm : (.all ((.impl P Q : BF L α 1).rename Sum.inl)) ∈ Δ := by
      apply Finset.mem_insert_of_mem
      refine Finset.mem_image.mpr ⟨.all (.impl P Q), by simp [Γ], ?_⟩
      exact Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst_all _ (fun x => .var (Sum.inl x))
    apply CoreProof.allLeft (.var (.inr 0)) hm
    rw [instantiate_fresh]
    change CoreProof L (insert (.impl P.toFormula Q.toFormula) Δ)
      ((.ex Q : Formula L α).rename Sum.inl)
    apply CoreProof.implLeft (Finset.mem_insert_self _ _)
    · exact CoreProof.identity _ ((Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.equalityFree_map _ _).mpr hP) (by simp [Δ])
    · rw [show (.ex Q : Formula L α).rename (Sum.inl : α → α ⊕ Fin 1) =
          .ex (Q.rename Sum.inl) from Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.subst_ex _ _]
      apply CoreProof.exRight (.var (.inr 0))
      rw [instantiate_fresh]
      exact CoreProof.identity _ ((Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.equalityFree_map _ _).mpr hQ)
        (Finset.mem_insert_self _ _)
  · intro A hA
    rcases Finset.mem_insert.mp hA with rfl | hA
    · exact ⟨hP, hQ⟩
    · have he := Finset.mem_singleton.mp hA
      subst A
      exact hP

private def identityFormula : Formula L α := .impl .falsum .falsum

/-- This particular equality-disabled tree introduces then eliminates a disjunction
containing equality, while retaining its pure ambient assumption. -/
def intermediateEquality (t : L.Term α) :
    Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Derivation false false L (α := α)
      {identityFormula} identityFormula := by
  apply Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.Derivation.disjElim (B := Lemmatheca.ProofTheory.FirstOrder.NaturalDeduction.termEqual t t)
    (.disjIntroLeft (.assumption (Finset.mem_singleton_self _)))
  · exact .assumption (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  · exact .assumption (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))

theorem intermediateEquality_endpoints (t : L.Term α) :
    ContextPure ({identityFormula} : Context L α) ∧
      (identityFormula : Formula L α).EqualityFree ∧ ¬ (intermediateEquality t).Pure := by
  refine ⟨?_, by simp [identityFormula, Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.EqualityFree], ?_⟩
  · intro A hA
    have he := Finset.mem_singleton.mp hA
    subst A
    trivial
  · intro h
    exact h.2.2.1.2.1.2

/-- The auxiliary variable with reserve index zero is the existential witness. -/
def constantFreeExistence :
    Proof Language.empty ∅
      Lemmatheca.Entry.IntuitionisticFirstOrderDeduction.constantFreeFormula := by
  change RawProof Language.empty (α := Empty ⊕ ℕ) ∅ (.ex (.impl .falsum .falsum))
  refine ⟨.exRight (.var (.inr 0)) (.implRight (.falsumLeft (Finset.mem_insert_self _ _))), ?_, by simp [Lemmatheca.ProofTheory.FirstOrder.BoundedFormula.EqualityFree]⟩
  intro A hA
  simp at hA

theorem constantFreeRawCutImpossible :
    ¬ Nonempty (RawCutProof Language.empty ∅
      Lemmatheca.Entry.IntuitionisticFirstOrderDeduction.constantFreeFormula) := by
  rintro ⟨p⟩
  exact Lemmatheca.Entry.IntuitionisticFirstOrderDeduction.constantFreeRawImpossible false false
    ⟨p.toNatural⟩

theorem constantFreeRawImpossible :
    ¬ Nonempty (RawProof Language.empty ∅
      Lemmatheca.Entry.IntuitionisticFirstOrderDeduction.constantFreeFormula) := by
  rintro ⟨p⟩
  exact constantFreeRawCutImpossible ⟨p.toCut⟩

theorem constantFreeNoGroundTerm : ¬ Nonempty (Language.empty.Term Empty) := by
  rintro ⟨t⟩
  cases t with
  | var x => exact x.elim
  | func f _ => exact f.elim

end
end Lemmatheca.Entry.EqualityFreeIntuitionisticFirstOrderSequents
