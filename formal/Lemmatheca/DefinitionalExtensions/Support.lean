import Lemmatheca.ChangingLanguages.ChangingLanguages

/-! Routine free-variable bookkeeping for the elimination construction. -/
namespace Lemmatheca.MathematicalLogic.DefinitionalExtensions.Support
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic.FirstOrderSyntax
noncomputable section
universe u v w z
variable {L : Language.{u,v}} {α : Type w} {β : Type z}
variable [DecidableEq α] [DecidableEq β]

def Uses (P : α → Prop) (A : L.Formula α) : Prop := ∀ a ∈ A.freeVarFinset, P a
def TermUses (P : α → Prop) (t : L.Term α) : Prop := ∀ a ∈ t.varFinset, P a

private def supportImage {α β : Type*} [DecidableEq β] {n : ℕ} (f : α → β ⊕ Fin n) (x : α) : Finset β :=
  match f x with | .inl y => {y} | .inr _ => ∅

private theorem term_relabelAux_support {n k : ℕ}
    (f : α → β ⊕ Fin n) (t : L.Term (α ⊕ Fin k)) :
    (t.relabel (BoundedFormula.relabelAux f k)).varFinsetLeft =
      t.varFinsetLeft.biUnion (supportImage f) := by
  induction t with
  | var x =>
    cases x with
    | inl x => cases hx : f x <;> simp [BoundedFormula.relabelAux, supportImage, hx]
    | inr x => simp [BoundedFormula.relabelAux]
  | func g ts ih => simp only [Term.relabel, Term.varFinsetLeft, ih, Finset.biUnion_biUnion]

private theorem formula_relabel_support {n k : ℕ}
    (f : α → β ⊕ Fin n) (A : L.BoundedFormula α k) :
    (A.relabel f).freeVarFinset = A.freeVarFinset.biUnion (supportImage f) := by
  induction A with
  | falsum => simp [BoundedFormula.relabel, BoundedFormula.mapTermRel]
  | equal s t => simp [BoundedFormula.relabel, BoundedFormula.mapTermRel,
      term_relabelAux_support, Finset.union_biUnion]
  | rel R ts => simp [BoundedFormula.relabel, BoundedFormula.mapTermRel,
      term_relabelAux_support, Finset.biUnion_biUnion]
  | imp A B ihA ihB => simp only [BoundedFormula.relabel_imp,
      BoundedFormula.freeVarFinset, ihA, ihB, Finset.union_biUnion]
  | all A ih => simpa only [BoundedFormula.relabel_all, BoundedFormula.freeVarFinset] using ih

theorem relabel_uses {A : L.Formula α} {f : α → β} {P : β → Prop}
    (h : Uses (P ∘ f) A) : Uses P (A.relabel f) := by
  intro b hb
  rw [Formula.relabel, formula_relabel_support] at hb
  obtain ⟨a, ha, hab⟩ := Finset.mem_biUnion.mp hb
  have he : f a = b := by simpa [supportImage, eq_comm] using hab
  exact he ▸ h a ha

theorem relabel_uses_all (A : L.Formula α) (f : α → β) (P : β → Prop)
    (h : ∀ a, P (f a)) : Uses P (A.relabel f) :=
  relabel_uses (fun a _ => h a)

private theorem alls_support {n : ℕ} (A : L.BoundedFormula α n) :
    A.alls.freeVarFinset = A.freeVarFinset := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih A.all

private theorem exs_support {n : ℕ} (A : L.BoundedFormula α n) :
    A.exs.freeVarFinset = A.freeVarFinset := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [BoundedFormula.exs, ih]
    simp

theorem iExs_uses {γ : Type*} [Finite γ] [DecidableEq γ] {A : L.Formula (α ⊕ γ)} {P : α → Prop}
    (h : Uses (Sum.elim P (fun _ => True)) A) : Uses P (A.iExs γ) := by
  intro a ha
  rw [Formula.iExs, exs_support, formula_relabel_support] at ha
  obtain ⟨b, hb, hab⟩ := Finset.mem_biUnion.mp ha
  cases b with
  | inl b =>
    have he : b = a := by simpa [supportImage, eq_comm] using hab
    exact he ▸ h (.inl b) hb
  | inr b => simp [supportImage] at hab

theorem iAlls_uses {γ : Type*} [Finite γ] [DecidableEq γ] {A : L.Formula (α ⊕ γ)} {P : α → Prop}
    (h : Uses (Sum.elim P (fun _ => True)) A) : Uses P (A.iAlls γ) := by
  intro a ha
  rw [Formula.iAlls, alls_support, formula_relabel_support] at ha
  obtain ⟨b, hb, hab⟩ := Finset.mem_biUnion.mp ha
  cases b with
  | inl b =>
    have he : b = a := by simpa [supportImage, eq_comm] using hab
    exact he ▸ h (.inl b) hb
  | inr b => simp [supportImage] at hab

theorem imp_uses {P : α → Prop} {A B : L.Formula α} (hA : Uses P A) (hB : Uses P B) :
    Uses P (A.imp B) := by
  intro a ha
  exact (Finset.mem_union.mp ha).elim (hA a) (hB a)

theorem bot_uses (P : α → Prop) : Uses P (⊥ : L.Formula α) := by
  intro a ha
  exact (Finset.notMem_empty a ha).elim

theorem inf_uses {P : α → Prop} {A B : L.Formula α} (hA : Uses P A) (hB : Uses P B) :
    Uses P (A ⊓ B) :=
  imp_uses (imp_uses hA (imp_uses hB (bot_uses P))) (bot_uses P)

theorem iInf_uses {γ : Type*} [Finite γ] {P : α → Prop} (A : γ → L.Formula α)
    (h : ∀ i, Uses P (A i)) : Uses P (Formula.iInf A) := by
  have hl (l : List γ) : Uses P ((l.map A).foldr (· ⊓ ·) ⊤) := by
    induction l with
    | nil => exact imp_uses (bot_uses P) (bot_uses P)
    | cons a l ih => exact inf_uses (h a) ih
  exact hl _

theorem term_inl_support (t : L.Term (α ⊕ β)) (a : α) :
    a ∈ t.varFinsetLeft ↔ Sum.inl a ∈ t.varFinset := by
  induction t with
  | var b => cases b <;> simp
  | func f ts ih => simp only [Term.varFinsetLeft, Term.varFinset, Finset.mem_biUnion, ih]

private theorem term_inl_image (t : L.Term α) :
    (t.relabel (Sum.inl : α → α ⊕ Fin 0)).varFinsetLeft = t.varFinset := by
  induction t with
  | var a => rfl
  | func f ts ih => simp only [Term.relabel, Term.varFinsetLeft, Term.varFinset, ih]

theorem equal_uses {P : α → Prop} {s t : L.Term α} (hs : TermUses P s) (ht : TermUses P t) :
    Uses P (s.equal t) := by
  intro a ha
  simp only [Term.equal, Term.bdEqual, BoundedFormula.freeVarFinset, term_inl_image,
    Finset.mem_union] at ha
  exact ha.elim (hs a) (ht a)

theorem subst_uses {γ : Type*} [DecidableEq γ] (A : L.Formula γ) (σ : γ → L.Term α) {P : α → Prop}
    (h : ∀ i, TermUses P (σ i)) : Uses P (A.subst σ) := by
  intro a ha
  rw [formula_freeVarFinset_subst] at ha
  obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp ha
  exact h i a hi

end
end Lemmatheca.MathematicalLogic.DefinitionalExtensions.Support
