import Lemmatheca.FiniteDimensionalFirstOrderInterpretations.Core
import Mathlib.Tactic.FinCases

namespace Lemmatheca.Entry.FiniteDimensionalFirstOrderInterpretations
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic.FiniteDimensionalInterpretations
open Lemmatheca.MathematicalLogic.FiniteDimensionalInterpretations.InterpretationData
noncomputable section
universe u v w
variable {K : Language.{u,v}}

def pairLanguage : Language := ⟨fun n => PLift (n = 1), fun n => PLift (n = 1)⟩

def pairData (s : K.Functions 1) (r : K.Relations 2) : InterpretationData pairLanguage K 2 where
  positive := by decide
  domain := ⊤
  functionGraph {n} f := by
    obtain ⟨hf⟩ := f
    cases hf
    exact Formula.iInf (fun j : Fin 2 =>
      (Term.var (.inr j)).equal (.func s (fun _ => .var (.inl (0,j)))))
  relationFormula {n} R := by
    obtain ⟨hR⟩ := R
    cases hR
    exact r.formula (fun j => .var (0,j))

variable (s : K.Functions 1) (r : K.Relations 2) {M : Type w} [K.Structure M]

private theorem pair_graph_iff (x : Fin 1 → (pairData s r).Domain M) (y : Fin 2 → M) :
    ((pairData s r).guardedGraph (⟨rfl⟩ : pairLanguage.Functions 1)).Realize
      (Sum.elim ((pairData s r).coordinates M x) y) ↔
      ∀ j, y j = Structure.funMap s (fun _ => (x 0).val j) := by
  simp only [guardedGraph, pairData, Formula.realize_inf, Formula.realize_relabel,
    Formula.realize_top, true_and, Formula.realize_iInf, Formula.realize_equal,
    Term.realize_var, Term.realize_func, Sum.elim_inr, Sum.elim_inl, coordinates]

theorem pair_good [Nonempty M] : (pairData s r).Good M := by
  refine ⟨⟨⟨fun _ => Classical.ofNonempty, ?_⟩⟩, ?_⟩
  · exact Formula.realize_top.mpr trivial
  · intro n f x
    obtain ⟨hf⟩ := f
    cases hf
    refine ⟨fun j => Structure.funMap s (fun _ => (x 0).val j), ?_, ?_⟩
    · exact (pair_graph_iff s r x _).mpr (fun _ => rfl)
    · intro y hy
      exact funext ((pair_graph_iff s r x y).mp hy)


theorem pair_function [Nonempty M] (a : (pairData s r).Domain M) (j : Fin 2) :
    let := (pairData s r).inducedStructure (pair_good s r (M := M)).2
    (@Structure.funMap pairLanguage ((pairData s r).Domain M) _ 1 ⟨rfl⟩
      (fun _ => a)).val j = Structure.funMap s (fun _ => a.val j) := by
  let := (pairData s r).inducedStructure (pair_good s r (M := M)).2
  have hg := ((pairData s r).induced_fun_graph (pair_good s r (M := M)).2
    (⟨rfl⟩ : pairLanguage.Functions 1) (fun _ => a) _).mpr rfl
  exact (pair_graph_iff s r (fun _ => a) _).mp hg j


theorem pair_relation [Nonempty M] (a : (pairData s r).Domain M) :
    let := (pairData s r).inducedStructure (pair_good s r (M := M)).2
    @Structure.RelMap pairLanguage ((pairData s r).Domain M) _ 1 ⟨rfl⟩ (fun _ => a) ↔
      Structure.RelMap r a.val := by
  let := (pairData s r).inducedStructure (pair_good s r (M := M)).2
  change ((pairData s r).relationFormula (⟨rfl⟩ : pairLanguage.Relations 1)).Realize
    ((pairData s r).coordinates M (fun _ => a)) ↔ _
  simp only [pairData, Formula.realize_rel, Term.realize_var, coordinates]


def doubleTerm : pairLanguage.Term Unit :=
  .func ⟨rfl⟩ (fun _ => .func ⟨rfl⟩ (fun _ => .var ()))

def pairSentence : pairLanguage.Sentence :=
  ((Relations.formula (⟨rfl⟩ : pairLanguage.Relations 1) (fun _ => doubleTerm)).relabel
    (Sum.inr : Unit → Empty ⊕ Unit)).iAlls Unit

theorem pair_double_graph [Nonempty M] (a : (pairData s r).Domain M) (y : Fin 2 → M) :
    ((pairData s r).termGraph doubleTerm).Realize
      (Sum.elim ((pairData s r).coordinates M (fun _ => a)) y) ↔
      ∀ j, y j = Structure.funMap s (fun _ =>
        Structure.funMap s (fun _ => a.val j)) := by
  let := (pairData s r).inducedStructure (pair_good s r (M := M)).2
  rw [(pairData s r).realize_termGraph (pair_good s r (M := M)).2]
  have hval : (doubleTerm.realize (fun _ : Unit => a)).val =
      fun j => Structure.funMap s (fun _ => Structure.funMap s (fun _ => a.val j)) := by
    funext j
    let b := @Structure.funMap pairLanguage ((pairData s r).Domain M) _ 1 ⟨rfl⟩ (fun _ => a)
    have h1 := pair_function s r b j
    have h0 := pair_function s r a j
    change (@Structure.funMap pairLanguage ((pairData s r).Domain M) _ 1 ⟨rfl⟩ (fun _ => b)).val j = _
    exact h1.trans (congrArg (fun z => Structure.funMap s (fun _ => z)) h0)
  rw [hval]
  exact funext_iff


theorem pair_sentence [Nonempty M] :
    M ⊨ (pairData s r).translateSentence pairSentence ↔
      ∀ a b : M, Structure.RelMap r
        ![Structure.funMap s (fun _ => Structure.funMap s (fun _ => a)),
          Structure.funMap s (fun _ => Structure.funMap s (fun _ => b))] := by
  let := (pairData s r).inducedStructure (pair_good s r (M := M)).2
  rw [(pairData s r).realize_translateSentence (pair_good s r (M := M)).2]
  change Formula.Realize pairSentence (default : Empty → (pairData s r).Domain M) ↔ _
  simp only [pairSentence, Formula.realize_iAlls, Formula.realize_relabel,
    Sum.elim_comp_inr]
  constructor
  · intro h a b
    let c : (pairData s r).Domain M := ⟨![a,b], Formula.realize_top.mpr trivial⟩
    have hc := h (fun _ => c)
    have heq : (doubleTerm.realize (fun _ : Unit => c)).val =
        ![Structure.funMap s (fun _ => Structure.funMap s (fun _ => a)),
          Structure.funMap s (fun _ => Structure.funMap s (fun _ => b))] := by
      have hg := (pair_double_graph s r c _).mp
        (((pairData s r).realize_termGraph (pair_good s r (M := M)).2 _ _ _).mpr rfl)
      funext j
      fin_cases j
      · exact hg 0
      · exact hg 1
    have hr := (pair_relation s r (doubleTerm.realize (fun _ : Unit => c))).mp hc
    exact heq ▸ hr
  · intro h x
    let c := x ()
    apply (pair_relation s r (doubleTerm.realize (fun _ : Unit => c))).mpr
    have heq : (doubleTerm.realize (fun _ : Unit => c)).val =
        ![Structure.funMap s (fun _ => Structure.funMap s (fun _ => c.val 0)),
          Structure.funMap s (fun _ => Structure.funMap s (fun _ => c.val 1))] := by
      have hg := (pair_double_graph s r c _).mp
        (((pairData s r).realize_termGraph (pair_good s r (M := M)).2 _ _ _).mpr rfl)
      funext j
      fin_cases j
      · exact hg 0
      · exact hg 1
    rw [heq]
    exact h (c.val 0) (c.val 1)


def diagonalGuard : K.Formula (Fin 2) := (Term.var 0).equal (.var 1)

theorem diagonal_projection (a : M) (j : Fin 2) :
    ∃ x : Fin 2 → M, (diagonalGuard (K := K)).Realize x ∧ x j = a := by
  refine ⟨fun _ => a, ?_, rfl⟩
  exact Formula.realize_equal.mpr rfl


theorem diagonal_counterexample (a b : M) (hab : a ≠ b) :
    ¬ (diagonalGuard (K := K)).Realize ![a,b] ∧
      (∀ j : Fin 2, ∃ x : Fin 2 → M, (diagonalGuard (K := K)).Realize x ∧ x j = (![a,b] : Fin 2 → M) j) := by
  refine ⟨?_, fun j => diagonal_projection (K := K) ((![a,b] : Fin 2 → M) j) j⟩
  simpa only [diagonalGuard, Formula.realize_equal, Term.realize_var,
    Matrix.cons_val_zero, Matrix.cons_val_one] using hab


theorem singleton_diagonal [Subsingleton M] (x : Fin 2 → M) :
    (diagonalGuard (K := K)).Realize x := by
  exact Formula.realize_equal.mpr (Subsingleton.elim _ _)


end
end Lemmatheca.Entry.FiniteDimensionalFirstOrderInterpretations
