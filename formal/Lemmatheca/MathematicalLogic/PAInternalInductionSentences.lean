import Lemmatheca.MathematicalLogic.PAInternalArithmeticSentences

/-! Closed PA assertions for the induction and finite-congruence facts used in
internal history coding. All quantifiers are in the shared arithmetic syntax. -/
namespace Lemmatheca.MathematicalLogic.PAComputations
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic ArithmeticTheories ArithmeticRepresentability FirstOrderProofs
noncomputable section

/-- Strong induction for the particular arithmetic formula and its parameters. -/
def strongInductionSentence {k : ℕ} (φ : language.Formula (Fin k ⊕ Unit)) :
    language.Sentence :=
  let smaller : language.Formula ((Fin k ⊕ Unit) ⊕ Unit) :=
    (ltFormula (.var (.inr ())) (.var (.inl (.inr ())))).imp
      (φ.relabel (Sum.elim (fun i => .inl (.inl i)) (fun _ => .inr ())))
  allClose ((((smaller.iAlls Unit).imp φ).iAlls Unit).imp (φ.iAlls Unit))

/-- Every positive number through the bound divides the proposed multiple. -/
def multiplesThrough {α : Type} (d n : language.Term α) : language.Formula α :=
  ((((Term.var (.inr ())).equal zeroTerm).not).imp
    ((leFormula (.var (.inr ())) (n.relabel Sum.inl)).imp
      (dividesFormula (.var (.inr ())) (d.relabel Sum.inl)))).iAlls Unit

def commonMultipleSentence : language.Sentence :=
  allClose (((((Term.var (.inr ())).equal zeroTerm).not) ⊓
    multiplesThrough (.var (.inr ())) (.var (.inl (0 : Fin 1)))).iExs Unit)

/-- The literal arithmetic term for the beta decoder's modulus. -/
def betaModulusTermAt {α : Type} (d i : language.Term α) : language.Term α :=
  succTerm (mulTerm (succTerm i) d)

def pairwiseModuliSentence : language.Sentence :=
  let d : language.Term (Fin 4) := .var 0
  let n : language.Term (Fin 4) := .var 1
  let i : language.Term (Fin 4) := .var 2
  let j : language.Term (Fin 4) := .var 3
  allClose ((multiplesThrough d (succTerm n)).imp
    ((leFormula i n).imp ((leFormula j n).imp
      ((i.equal j).not.imp (coprimeFormula (betaModulusTermAt d i) (betaModulusTermAt d j))))))

theorem realize_multiplesThrough {α : Type} {M : Type*} [language.Structure M]
    (d n : language.Term α) (v : α → M) :
    (multiplesThrough d n).Realize v ↔
      ∀ j : M, j ≠ zeroValue M → leValue M j (n.realize v) →
        DividesModel M j (d.realize v) := by
  simp only [multiplesThrough, Formula.realize_iAlls, Formula.realize_imp,
    Formula.realize_not, Formula.realize_equal, Term.realize_var, realize_zeroTerm,
    realize_leFormula, realize_dividesFormula, Term.realize_relabel,
    Function.comp_def, Sum.elim_inl, Sum.elim_inr]
  exact ⟨fun h j => h (fun _ => j), fun h j => h (j ())⟩

theorem strong_induction_derives {k : ℕ} (φ : language.Formula (Fin k ⊕ Unit)) :
    Derives PA (strongInductionSentence φ) := by
  apply derives_allClose_of_models
  intro M v
  simp only [Formula.realize_imp, Formula.realize_iAlls, Formula.realize_relabel,
    ltFormula, realize_leFormula, realize_succTerm, Term.realize_var,
    Function.comp_def, Sum.elim_inl, Sum.elim_inr]
  intro hs a
  let P : M → Prop := fun x => φ.Realize (extend v x)
  have hP : Set.univ.Definable₁ language {x | P x} := by
    change DPred (fun w : Fin 1 → M => φ.Realize (extend v (w 0)))
    apply dp_formula φ
    intro i
    cases i with
    | inl i => exact df_const (v i)
    | inr i => exact df_proj 0
  have hstep (x : M) (ih : ∀ y, leValue M (succValue M y) x → P y) : P x := by
    apply hs (fun _ => x)
    intro y hy
    have he : (fun i => Sum.elim (Sum.elim v (fun _ : Unit => x)) y
        (Sum.elim (fun i => Sum.inl (Sum.inl i)) (fun _ => Sum.inr ()) i)) =
        extend v (y ()) := by
      funext i
      cases i <;> rfl
    rw [he]
    exact ih (y ()) hy
  exact definable_strong_induction P hP hstep (a ())

theorem common_multiple_derives : Derives PA commonMultipleSentence := by
  apply derives_allClose_of_models
  intro M v
  simp only [Formula.realize_iExs, Formula.realize_inf, Formula.realize_not,
    Formula.realize_equal, Term.realize_var, realize_zeroTerm,
    realize_multiplesThrough, Sum.elim_inl, Sum.elim_inr]
  obtain ⟨d, hd, hm⟩ := common_multiple_model (v 0)
  exact ⟨fun _ => d, hd, hm⟩

theorem pairwise_moduli_derives : Derives PA pairwiseModuliSentence := by
  apply derives_allClose_of_models
  intro M v
  simp only [Formula.realize_imp, realize_multiplesThrough, realize_leFormula,
    Formula.realize_not, Formula.realize_equal, realize_coprimeFormula,
    Term.realize_var, realize_succTerm, betaModulusTermAt, realize_mulTerm]
  intro hm hi hj hne
  exact betaModulus_pairwise_model (v 0) (v 1) hm (v 2) (v 3) hi hj hne

end
end Lemmatheca.MathematicalLogic.PAComputations
