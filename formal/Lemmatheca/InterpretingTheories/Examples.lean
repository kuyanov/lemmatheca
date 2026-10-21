import Lemmatheca.InterpretingTheories.Composition
import Lemmatheca.DefinitionalExtensions.Examples
import Lemmatheca.FirstOrderStructures.FirstOrderSemantics

namespace Lemmatheca.Entry.InterpretingTheories
open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic.InterpretingTheories
open Lemmatheca.MathematicalLogic.InterpretingTheories.InterpretationData
open Lemmatheca.MathematicalLogic.FirstOrderProofs
open Lemmatheca.MathematicalLogic.DefinitionalExtensions (close)
open Lemmatheca.Entry.DefinitionalExtensions (functionLanguage)
noncomputable section
universe u v w
variable {K : Language.{u,v}}

def emptyDomain : InterpretationData Language.empty K where
  domain := ⊥
  functionGraph f := f.elim
  relationFormula R := R.elim

theorem empty_domain_counterexample {M : Type w} [K.Structure M] [Nonempty M] :
    letI : Language.empty.Structure M := Language.emptyStructure
    (M ⊨ Lemmatheca.MathematicalLogic.FirstOrderSemantics.existsSelfEqual Language.empty) ∧
      ¬ (M ⊨ (emptyDomain (K := K)).translateSentence
        (Lemmatheca.MathematicalLogic.FirstOrderSemantics.existsSelfEqual Language.empty)) := by
  let : Language.empty.Structure M := Language.emptyStructure
  constructor
  · exact Lemmatheca.MathematicalLogic.FirstOrderSemantics.existsSelfEqual_realize.mpr inferInstance
  · intro ht
    have hG : (emptyDomain (K := K)).GoodGraphs M := relational_graphs
    let := (emptyDomain (K := K)).inducedStructure hG
    have hs := (realize_translateSentence hG _).mp ht
    obtain ⟨a⟩ := Lemmatheca.MathematicalLogic.FirstOrderSemantics.existsSelfEqual_realize.mp hs
    exact a.property

def successorData (P : K.Relations 1) (s : K.Functions 1) :
    InterpretationData (functionLanguage 1) K where
  domain := P.formula (fun _ => .var ())
  functionGraph {n} f := by
    obtain ⟨hf⟩ := f
    cases hf
    exact (Term.var (.inr ())).equal (.func s (fun _ => .var (.inl 0)))
  relationFormula R := R.elim

def closureSentence (P : K.Relations 1) (s : K.Functions 1) : K.Sentence :=
  close ((P.formula (Term.var : Fin 1 → K.Term (Fin 1))).imp
    (P.formula (fun _ => .func s (fun _ => .var 0))))

theorem successor_graph_condition (P : K.Relations 1) (s : K.Functions 1)
    {M : Type w} [K.Structure M] (a : (successorData P s).Domain M) :
    (∃! y : M, ((successorData P s).guardedGraph ⟨rfl⟩).Realize
      (Sum.elim (fun _ => a.val) (fun _ => y))) ↔
      Structure.RelMap P (fun _ => Structure.funMap s (fun _ => a.val)) := by
  simp only [guardedGraph, successorData, Formula.realize_inf, Formula.realize_relabel,
    Sum.elim_comp_inr, Formula.realize_rel, Term.realize_var, Formula.realize_equal,
    Sum.elim_inr, Term.realize_func, Sum.elim_inl]
  constructor
  · rintro ⟨y, ⟨hy, he⟩, _⟩
    simpa only [he] using hy
  · intro hy
    exact ⟨Structure.funMap s (fun _ => a.val), ⟨hy, rfl⟩, fun y h => h.2⟩

theorem successor_admissible (P : K.Relations 1) (s : K.Functions 1) {S : K.Theory}
    (hN : Derives S (successorData P s).nonemptySentence)
    (hC : Derives S (closureSentence P s)) : (successorData P s).Admissible S := by
  refine ⟨hN, ?_⟩
  intro n f
  obtain ⟨hf⟩ := f
  cases hf
  apply Lemmatheca.MathematicalLogic.ChangingLanguages.deductive_completeness
  rw [Theory.models_sentence_iff]
  intro M
  apply ((successorData P s).realize_graphSentence ⟨rfl⟩).mpr
  intro x hx
  have hx0 := hx 0
  have hconst : x = fun _ => x 0 := by
    funext i
    rw [Fin.eq_zero i]
  rw [hconst]
  apply (successor_graph_condition P s ⟨x 0, hx0⟩).mpr
  have hc : M ⊨ closureSentence P s :=
    derives_sound hC default (fun A hA => Theory.realize_sentence_of_mem S hA)
  rw [closureSentence, Lemmatheca.MathematicalLogic.DefinitionalExtensions.realize_close] at hc
  have hp := hc (fun _ => x 0)
  simp only [Formula.realize_imp, Formula.realize_rel, Term.realize_var,
    Term.realize_func] at hp
  apply hp
  simpa only [successorData, Formula.realize_rel, Term.realize_var] using hx0

theorem successor_interprets_empty (P : K.Relations 1) (s : K.Functions 1) {S : K.Theory}
    (hN : Derives S (successorData P s).nonemptySentence)
    (hC : Derives S (closureSentence P s)) :
    (successorData P s).Interprets (∅ : (functionLanguage 1).Theory) S := by
  exact ⟨successor_admissible P s hN hC, fun A hA => hA.elim⟩

def predicateSuccessorLanguage : Language := ⟨fun n => PLift (n = 1), fun n => PLift (n = 1)⟩

@[instance_reducible] def predicateSuccessorStructure {M : Type w} (P : M → Prop) (s : M → M) :
    predicateSuccessorLanguage.Structure M where
  funMap {n} f x := by
    obtain ⟨hf⟩ := f
    cases hf
    exact s (x 0)
  RelMap {n} R x := by
    obtain ⟨hR⟩ := R
    cases hR
    exact P (x 0)

def selectedSuccessor : InterpretationData (functionLanguage 1) predicateSuccessorLanguage :=
  successorData ⟨rfl⟩ ⟨rfl⟩

theorem closure_counterexample :
    letI := predicateSuccessorStructure (fun b : Bool => b = false) (fun _ => true)
    Nonempty (selectedSuccessor.Domain Bool) ∧ ¬ selectedSuccessor.GoodGraphs Bool := by
  let := predicateSuccessorStructure (fun b : Bool => b = false) (fun _ => true)
  have ha : selectedSuccessor.domain.Realize (fun _ => false) := by rfl
  refine ⟨⟨⟨false, ha⟩⟩, ?_⟩
  intro h
  have hx := h 1 ⟨rfl⟩ (fun _ => ⟨false, ha⟩)
  have hp := (successor_graph_condition (K := predicateSuccessorLanguage) (M := Bool)
    (⟨rfl⟩ : predicateSuccessorLanguage.Relations 1)
    (⟨rfl⟩ : predicateSuccessorLanguage.Functions 1) ⟨false, ha⟩).mp hx
  change true = false at hp
  exact Bool.noConfusion hp

theorem positive_successor :
    letI := predicateSuccessorStructure (fun n : ℕ => 1 ≤ n) Nat.succ
    selectedSuccessor.Good ℕ := by
  let := predicateSuccessorStructure (fun n : ℕ => 1 ≤ n) Nat.succ
  refine ⟨⟨⟨1, ?_⟩⟩, ?_⟩
  · change 1 ≤ 1
    exact le_rfl
  · intro n f x
    obtain ⟨hf⟩ := f
    cases hf
    have hconst : (fun i => (x i).val) = (fun _ : Fin 1 => (x 0).val) := by
      funext i
      rw [Fin.eq_zero i]
    rw [hconst]
    apply (successor_graph_condition (K := predicateSuccessorLanguage) (M := ℕ)
      (⟨rfl⟩ : predicateSuccessorLanguage.Relations 1)
      (⟨rfl⟩ : predicateSuccessorLanguage.Functions 1) (x 0)).mpr
    change 1 ≤ Nat.succ (x 0).val
    exact Nat.succ_pos _

theorem positive_successor_value (a : {n : ℕ // 1 ≤ n}) :
    letI := predicateSuccessorStructure (fun n : ℕ => 1 ≤ n) Nat.succ
    letI := selectedSuccessor.inducedStructure positive_successor.2
    (@Structure.funMap (functionLanguage 1) (selectedSuccessor.Domain ℕ) _ 1 ⟨rfl⟩
      (fun _ => (⟨a.val, a.property⟩ : selectedSuccessor.Domain ℕ))).val = a.val + 1 := by
  let := predicateSuccessorStructure (fun n : ℕ => 1 ≤ n) Nat.succ
  let := selectedSuccessor.inducedStructure positive_successor.2
  have hg := (selectedSuccessor.induced_fun_graph positive_successor.2 ⟨rfl⟩
    (fun _ => (⟨a.val, a.property⟩ : selectedSuccessor.Domain ℕ)) _).mpr rfl
  have he := (Formula.realize_inf.mp hg).2
  change _ = a.val + 1 at he
  exact he

end
end Lemmatheca.Entry.InterpretingTheories
