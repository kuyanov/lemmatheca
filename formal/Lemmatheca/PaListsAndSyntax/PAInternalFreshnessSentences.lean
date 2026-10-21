import Lemmatheca.PaListsAndSyntax.PAInternalSyntaxSentences

open Lemmatheca.MathematicalLogic Lemmatheca.ModelTheory Lemmatheca.ComputabilityTheory

/-! Closed PA assertions for conditional list and freshness identities. -/
namespace Lemmatheca.ProofTheory.PAComputations
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic ArithmeticTheories ArithmeticRepresentability FirstOrderProofs
open ProofPrograms ProofPrograms.SyntaxPrograms
noncomputable section

/-- Equality of the unique values of the specified graph presentations. -/
def programEquation {r : ℕ} (p q : Program r) : language.Formula (Fin r) :=
  (p.graph ⊓ q.graph).iExs Unit

theorem realize_programEquation {r : ℕ} (p q : Program r)
    (M : Theory.ModelType.{0,0,0} PA) (v : Fin r → M) :
    (programEquation p q).Realize v ↔ p.value v = q.value v := by
  rw [programEquation, Formula.realize_iExs]
  constructor
  · rintro ⟨a, ha⟩
    have hv : Sum.elim v a = extend v (a ()) := by funext i; cases i <;> rfl
    rw [Formula.realize_inf, hv] at ha
    exact ((p.value_iff v _).mp ha.1).symm.trans ((q.value_iff v _).mp ha.2)
  · intro h
    refine ⟨fun _ => p.value v, Formula.realize_inf.mpr ⟨?_, ?_⟩⟩
    · exact (p.value_iff v _).mpr rfl
    · exact (q.value_iff v _).mpr h

def listReconstructionSentence : language.Sentence :=
  let p : Program 1 := binary listCons (unary listHead (.proj 0)) (unary listTail (.proj 0))
  allClose (((Term.var (0 : Fin 1)).equal zeroTerm).not.imp (programEquation p (.proj 0)))

theorem list_reconstruction_derives : Derives PA listReconstructionSentence := by
  apply derives_allClose_of_models
  intro M v
  simp only [Formula.realize_imp, Formula.realize_not, Formula.realize_equal,
    Term.realize_var, realize_zeroTerm, realize_programEquation, binary_value,
    unary_value, Program.value_proj]
  exact cons_head_tail_value (v 0)

def tailSmallerSentence : language.Sentence :=
  let c : language.Term (Fin 1 ⊕ Unit) := .var (.inl 0)
  let a : language.Term (Fin 1 ⊕ Unit) := .var (.inr ())
  allClose ((c.equal zeroTerm).not.imp
    ((listTail.graph).imp (ltFormula a c)))

theorem tail_smaller_derives : Derives PA tailSmallerSentence := by
  apply derives_allClose_of_models
  intro M v
  simp only [Formula.realize_imp, Formula.realize_not, Formula.realize_equal,
    Term.realize_var, realize_zeroTerm, ltFormula, realize_leFormula, realize_succTerm]
  intro hc ht
  let c := v (.inl (0 : Fin 1))
  have hv : extend (fun _ : Fin 1 => c) (v (.inr ())) = v := by
    funext j
    cases j with
    | inl j => have hj : j = 0 := Subsingleton.elim _ _; subst j; rfl
    | inr j => cases j; rfl
  have he := (listTail.value_iff (fun _ : Fin 1 => c) (v (.inr ()))).mp (hv.symm ▸ ht)
  rw [he]
  have hx : (fun _ : Fin 1 => c) = ![c] := by funext i; fin_cases i; rfl
  simpa only [hx, c] using tail_smaller_value c hc

def numeralFreshProgram : Program 2 :=
  .comp CheckerPrograms.occursAux ![.proj 0, unary numeral (.proj 1)]

theorem numeral_fresh_derives : PAEquivalent numeralFreshProgram.graph (constant (r := 2) 0).graph := by
  apply Program.equivalent_of_values
  intro M x
  rw [numeralFreshProgram, Program.value_comp_two, unary_value, Program.value_proj,
    Program.value_proj, constant_value, numeral_value_zero]
  exact CheckerPrograms.numeral_occursAux_zero (x 0) (x 1)

def sentenceFreshSentence : language.Sentence :=
  allClose ((unary CheckerPrograms.isSentence (.proj (1 : Fin 2))).oneFormula.imp
    (programEquation (.comp CheckerPrograms.occursAux ![.proj 0, .proj 1]) (constant 0)))

theorem sentence_fresh_derives : Derives PA sentenceFreshSentence := by
  apply derives_allClose_of_models
  intro M v
  simp only [Formula.realize_imp, Program.realize_oneFormula, realize_programEquation,
    unary_value, Program.value_proj, Program.value_comp_two, constant_value, numeral_value_zero]
  exact CheckerPrograms.isSentence_occursAux_zero (v 0) (v 1)

def syntaxComponent (i : Fin 4) : Program 2 :=
  unary (part i) (unary stats (.proj 1))

def formulaFreshSentence : language.Sentence :=
  allClose ((programEquation (syntaxComponent 1) (constant 0)).not.imp
    ((programEquation (syntaxComponent 3) (constant 0)).imp
      (programEquation (.comp CheckerPrograms.occursAux ![.proj 0, .proj 1]) (constant 0))))

theorem formula_fresh_derives : Derives PA formulaFreshSentence := by
  apply derives_allClose_of_models
  intro M v
  simp only [Formula.realize_imp, Formula.realize_not, realize_programEquation,
    syntaxComponent, unary_value, Program.value_proj, constant_value, numeral_value_zero,
    Program.value_comp_two]
  exact (CheckerPrograms.recognized_noAux (v 0) (v 1)).2

end
end Lemmatheca.ProofTheory.PAComputations
