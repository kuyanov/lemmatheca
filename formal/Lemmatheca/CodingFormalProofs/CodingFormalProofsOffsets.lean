import Lemmatheca.CodingFormalProofs.CodingFormalProofsRelabel

open Lemmatheca.MathematicalLogic Lemmatheca.ModelTheory Lemmatheca.ComputabilityTheory

namespace Lemmatheca.ProofTheory.CodingFormalProofs
open FirstOrder FirstOrder.Language
universe u v
variable {L : Language.{u,v}} (S : EffectiveSignature L)

def codeAt {α : Type*} (name : α → ℕ) (o : ℕ) {n : ℕ} : L.BoundedFormula α n → ℕ
  | .falsum => botCode
  | .equal s t => equalCode (termCode S (Sum.elim name (fun j => boundName (o+j.val))) s)
      (termCode S (Sum.elim name (fun j => boundName (o+j.val))) t)
  | @BoundedFormula.rel _ _ n k r ts => node 5 (S.relationCode r :: List.ofFn (fun i : Fin k =>
      termCode S (Sum.elim name (fun j => boundName (o+j.val))) (ts i)))
  | .imp a b => impCode (codeAt name o a) (codeAt name o b)
  | .all a => allCode (codeAt name o a)

@[simp] theorem codeAt_zero {α : Type*} (name : α → ℕ) {n} (a : L.BoundedFormula α n) :
    codeAt S name 0 a = formulaCode S name a := by
  induction a with
  | falsum => rfl
  | equal s t => simp [codeAt,formulaCode]
  | rel r ts => simp [codeAt,formulaCode]
  | imp a b iha ihb => simp only [codeAt,formulaCode,iha,ihb]
  | all a ih => simp only [codeAt,formulaCode,ih]

theorem codeAt_cast {α : Type*} (name : α → ℕ) (o : ℕ) {m n}
    (h : m ≤ n) (a : L.BoundedFormula α m) :
    codeAt S name o (a.castLE h) = codeAt S name o a := by
  have hn (m n : ℕ) (h : m ≤ n) : (Sum.elim name (fun i : Fin n => boundName (o+i.val))) ∘
      Sum.map id (Fin.castLE h) = Sum.elim name (fun i : Fin m => boundName (o+i.val)) := by
    funext x
    cases x <;> rfl
  induction a generalizing n with
  | falsum => rfl
  | equal s t => simp only [BoundedFormula.castLE,codeAt,termCode_relabel,hn]
  | rel r ts => simp only [BoundedFormula.castLE,codeAt,Function.comp_apply,termCode_relabel,hn]
  | imp a b iha ihb =>
    simpa only [BoundedFormula.castLE,codeAt] using congrArg₂ impCode (iha h) (ihb h)
  | all a ih => simpa only [BoundedFormula.castLE,codeAt] using congrArg allCode (ih (Nat.succ_le_succ h))

theorem codeAt_relabel {α β : Type*} (name : β → ℕ) (o : ℕ) {m n}
    (f : α → β ⊕ Fin m) (a : L.BoundedFormula α n) :
    codeAt S name o (a.relabel f) =
      codeAt S (fun x => Sum.elim name (fun j => boundName (o+j.val)) (f x)) (o+m) a := by
  have hn (k : ℕ) : (Sum.elim name (fun j : Fin (m+k) => boundName (o+j.val))) ∘
      BoundedFormula.relabelAux f k =
      Sum.elim (fun x => Sum.elim name (fun j => boundName (o+j.val)) (f x))
        (fun j : Fin k => boundName (o+m+j.val)) := by
    funext x
    cases x with
    | inl x => cases h : f x <;> simp [BoundedFormula.relabelAux,h]
    | inr j => simp [BoundedFormula.relabelAux,Nat.add_assoc]
  induction a with
  | falsum => rfl
  | equal s t =>
    simp only [BoundedFormula.relabel,BoundedFormula.mapTermRel,codeAt,termCode_relabel,hn]
  | rel r ts =>
    simp only [BoundedFormula.relabel,BoundedFormula.mapTermRel,codeAt,termCode_relabel,hn,id_eq]
  | imp a b iha ihb => simp only [BoundedFormula.relabel_imp,codeAt,iha,ihb]
  | all a ih =>
    simp only [BoundedFormula.relabel,BoundedFormula.mapTermRel,codeAt,codeAt_cast]
    exact congrArg allCode ih

theorem codeAt_toFormula {α : Type*} (name : α → ℕ) (o : ℕ) {n}
    (a : L.BoundedFormula α n) :
    codeAt S (Sum.elim name (fun j : Fin n => boundName (o+j.val))) (o+n) a.toFormula =
      codeAt S name o a := by
  have hn (n : ℕ) : (Sum.elim (Sum.elim name (fun j : Fin n => boundName (o+j.val)))
      (fun j : Fin 0 => boundName (o+n+j.val))) ∘ Sum.inl =
      Sum.elim name (fun j : Fin n => boundName (o+j.val)) := by rfl
  induction a with
  | falsum => rfl
  | equal s t =>
    simp only [BoundedFormula.toFormula,Term.equal,Term.bdEqual,codeAt,termCode_relabel,hn]
  | rel r ts =>
    simp only [BoundedFormula.toFormula,Relations.formula,Relations.boundedFormula,codeAt,
      termCode_relabel,hn]
  | imp a b iha ihb => simp only [BoundedFormula.toFormula,codeAt,iha,ihb]
  | @all n a ih =>
    simp only [BoundedFormula.toFormula,codeAt,codeAt_relabel]
    have hh : (fun x : α ⊕ Fin (n+1) =>
        Sum.elim (Sum.elim name (fun j : Fin n => boundName (o+j.val)))
          (fun j : Fin 1 => boundName (o+n+j.val))
          ((Sum.elim (Sum.inl ∘ Sum.inl)
            (Sum.map Sum.inr id ∘ finSumFinEquiv.symm)) x)) =
        Sum.elim name (fun j : Fin (n+1) => boundName (o+j.val)) := by
      funext x
      cases x with
      | inl x => rfl
      | inr j =>
        rcases h : finSumFinEquiv.symm j with k | k
        · have hj := congrArg finSumFinEquiv h
          simp only [Equiv.apply_symm_apply,finSumFinEquiv_apply_left] at hj
          subst j
          simp [h]
        · have hj := congrArg finSumFinEquiv h
          simp only [Equiv.apply_symm_apply,finSumFinEquiv_apply_right] at hj
          subst j
          simp [h]
    rw [hh]
    simpa only [Nat.add_assoc] using congrArg allCode ih

end Lemmatheca.ProofTheory.CodingFormalProofs
