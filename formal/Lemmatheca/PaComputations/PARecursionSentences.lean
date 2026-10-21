import Lemmatheca.PaComputations.PAComputationsSentences

open Lemmatheca.MathematicalLogic Lemmatheca.ModelTheory Lemmatheca.ComputabilityTheory

namespace Lemmatheca.ProofTheory.PAComputations
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic ArithmeticTheories ArithmeticRepresentability FirstOrderProofs
noncomputable section
universe u

def recursionZeroFormula {n : ℕ} (R : language.Formula (Fin (n + 1) ⊕ Unit))
    (B : language.Formula (Fin n ⊕ Unit)) : language.Formula (Fin n ⊕ Unit) :=
  (graphAt R (Fin.snoc (fun i => .var (.inl i)) zeroTerm) (.var (.inr ()))).iff B

def recursionSuccessorFormula {n : ℕ} (R : language.Formula (Fin (n + 1) ⊕ Unit))
    (H : language.Formula (Fin (n + 2) ⊕ Unit)) : language.Formula (Fin (n + 1) ⊕ Unit) :=
  let x : Fin n → language.Term (Fin (n + 1) ⊕ Unit) := fun i => .var (.inl i.castSucc)
  let k : language.Term (Fin (n + 1) ⊕ Unit) := .var (.inl (Fin.last n))
  let y : language.Term (Fin (n + 1) ⊕ Unit) := .var (.inr ())
  let rhs : language.Formula ((Fin (n + 1) ⊕ Unit) ⊕ Unit) :=
    (graphAt R (Fin.snoc (fun i => (x i).relabel Sum.inl) (k.relabel Sum.inl)) (.var (.inr ()))) ⊓
    (graphAt H (Fin.snoc (Fin.snoc (fun i => (x i).relabel Sum.inl) (k.relabel Sum.inl))
      (.var (.inr ()))) (y.relabel Sum.inl))
  (graphAt R (Fin.snoc x (succTerm k)) y).iff (rhs.iExs Unit)

private theorem realize_snoc {α : Type} {n : ℕ} {M : Type u} [language.Structure M]
    (t : Fin n → language.Term α) (a : language.Term α) (v : α → M) :
    (fun i : Fin (n + 1) => ((Fin.snoc t a : Fin (n + 1) → language.Term α) i).realize v) = Fin.snoc (fun i => (t i).realize v) (a.realize v) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp

theorem realize_recursionZeroFormula {n : ℕ} {M : Type u} [language.Structure M]
    (R : language.Formula (Fin (n + 1) ⊕ Unit)) (B : language.Formula (Fin n ⊕ Unit))
    (x : Fin n → M) (y : M) :
    (recursionZeroFormula R B).Realize (extend x y) ↔
      (R.Realize (extend (Fin.snoc x (zeroValue M)) y) ↔ B.Realize (extend x y)) := by
  simp [recursionZeroFormula, realize_graphAt, realize_snoc, extend]

theorem realize_recursionSuccessorFormula {n : ℕ} {M : Type u} [language.Structure M]
    (R : language.Formula (Fin (n + 1) ⊕ Unit))
    (H : language.Formula (Fin (n + 2) ⊕ Unit)) (x : Fin n → M) (k y : M) :
    (recursionSuccessorFormula R H).Realize (extend (Fin.snoc x k) y) ↔
      (R.Realize (extend (Fin.snoc x (succValue M k)) y) ↔
        ∃ a, R.Realize (extend (Fin.snoc x k) a) ∧
          H.Realize (extend (Fin.snoc (Fin.snoc x k) a) y)) := by
  simp only [recursionSuccessorFormula, Formula.realize_iff, realize_graphAt,
    Formula.realize_iExs, Formula.realize_inf, realize_snoc,
    Term.realize_var, Term.realize_relabel, realize_succTerm,
    Function.comp_def, extend, Sum.elim_inl, Sum.elim_inr,
    Fin.snoc_castSucc, Fin.snoc_last]
  constructor
  · intro h
    constructor
    · intro hr
      obtain ⟨a, ha, hb⟩ := h.mp hr
      exact ⟨a (), ha, hb⟩
    · rintro ⟨a, ha, hb⟩
      exact h.mpr ⟨fun _ => a, ha, hb⟩
  · intro h
    constructor
    · intro hr
      obtain ⟨a, ha, hb⟩ := h.mp hr
      exact ⟨fun _ => a, ha, hb⟩
    · rintro ⟨a, ha, hb⟩
      exact h.mpr ⟨a (), ha, hb⟩

private theorem normalized_realize {n : ℕ} (p : Program n)
    (M : Theory.ModelType.{0,0,0} PA) (v : Fin n ⊕ Unit → M) :
    p.sigmaGraph.Realize v ↔ p.graph.Realize v := by
  exact (Formula.realize_iff.mp ((realize_allClose _).mp
    (derives_sound p.sigmaGraph_equivalent default
      (fun B hB => Theory.realize_sentence_of_mem PA hB)) v)).symm

theorem recursion_equations_derives {n : ℕ}
    (base : language.Formula (Fin n ⊕ Unit))
    (step : language.Formula (Fin (n + 2) ⊕ Unit)) :
    Derives PA (allClose (recursionZeroFormula (recursionGraph betaGraph base step) base)) ∧
    Derives PA (allClose (recursionSuccessorFormula (recursionGraph betaGraph base step) step)) := by
  constructor
  · apply derives_allClose_of_models
    intro M v
    let x : Fin n → M := fun i => v (.inl i)
    let y := v (.inr ())
    have hv : extend x y = v := by funext j; cases j with
      | inl j => rfl
      | inr j => cases j; rfl
    rw [← hv, realize_recursionZeroFormula]
    exact (recursion_equations_model base step x (zeroValue M) y).1
  · apply derives_allClose_of_models
    intro M v
    let x : Fin n → M := fun i => v (.inl i.castSucc)
    let k := v (.inl (Fin.last n))
    let y := v (.inr ())
    have hv : extend (Fin.snoc x k) y = v := by
      funext j
      cases j with
      | inl j => refine Fin.lastCases ?_ (fun i => ?_) j <;> simp [extend, x, k]
      | inr j => cases j; rfl
    rw [← hv, realize_recursionSuccessorFormula]
    exact (recursion_equations_model base step x k y).2

theorem Program.recursion_equations_derives {n : ℕ} (f : Program n) (g : Program (n + 2)) :
    Derives PA (allClose (recursionZeroFormula (Program.prec f g).graph f.graph)) ∧
    Derives PA (allClose (recursionSuccessorFormula (Program.prec f g).graph g.graph)) :=
  PAComputations.recursion_equations_derives f.graph g.graph

theorem Program.sigmaGraph_recursion_equations {n : ℕ} (f : Program n) (g : Program (n + 2)) :
    Derives PA (allClose (recursionZeroFormula (Program.prec f g).sigmaGraph f.sigmaGraph)) ∧
    Derives PA (allClose (recursionSuccessorFormula (Program.prec f g).sigmaGraph g.sigmaGraph)) := by
  constructor
  · apply derives_allClose_of_models
    intro M v
    let x : Fin n → M := fun i => v (.inl i)
    let y := v (.inr ())
    have hv : extend x y = v := by funext j; cases j with
      | inl j => rfl
      | inr j => cases j; rfl
    rw [← hv, realize_recursionZeroFormula]
    simpa only [normalized_realize] using (Program.recursion_equations f g x (zeroValue M) y).1
  · apply derives_allClose_of_models
    intro M v
    let x : Fin n → M := fun i => v (.inl i.castSucc)
    let k := v (.inl (Fin.last n))
    let y := v (.inr ())
    have hv : extend (Fin.snoc x k) y = v := by
      funext j
      cases j with
      | inl j => refine Fin.lastCases ?_ (fun i => ?_) j <;> simp [extend, x, k]
      | inr j => cases j; rfl
    rw [← hv, realize_recursionSuccessorFormula]
    simpa only [normalized_realize] using (Program.recursion_equations f g x k y).2

end
end Lemmatheca.ProofTheory.PAComputations
