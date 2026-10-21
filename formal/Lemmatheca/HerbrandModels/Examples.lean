import Lemmatheca.HerbrandModels.HerbrandModels

/-! Concrete ground instances and the two hypotheses that prevent false models. -/
namespace Lemmatheca.Entry.HerbrandModels

open FirstOrder FirstOrder.Language
open Lemmatheca.MathematicalLogic.Propositional
open Lemmatheca.MathematicalLogic.HerbrandModels

noncomputable section

inductive Functions : ℕ → Type
  | c : Functions 0
  | f : Functions 1

inductive Relations : ℕ → Type
  | p : Relations 1

def exampleLanguage : Language := ⟨Functions, Relations⟩

def c : GroundTerm exampleLanguage := .func Functions.c Fin.elim0
def f (t : GroundTerm exampleLanguage) : GroundTerm exampleLanguage :=
  .func Functions.f (fun _ => t)
def iterate : ℕ → GroundTerm exampleLanguage
  | 0 => c
  | n + 1 => f (iterate n)

private def depth : GroundTerm exampleLanguage → ℕ
  | .var x => x.elim
  | .func .c _ => 0
  | .func .f ts => depth (ts 0) + 1

private theorem iterate_depth (n : ℕ) : depth (iterate n) = n := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [iterate, f, depth] using congrArg (· + 1) ih

theorem ground_terms_unique (t : GroundTerm exampleLanguage) :
    ∃! n : ℕ, t = iterate n := by
  have he : ∃ n : ℕ, t = iterate n := by
    induction t with
    | var x => exact x.elim
    | func g ts ih =>
      cases g with
      | c =>
        refine ⟨0, ?_⟩
        change Term.func Functions.c ts = Term.func Functions.c Fin.elim0
        congr 1
        funext i
        exact i.elim0
      | f =>
        obtain ⟨n, hn⟩ := ih 0
        refine ⟨n + 1, ?_⟩
        change Term.func Functions.f ts = Term.func Functions.f (fun _ => iterate n)
        congr 1
        funext i
        have hi : i = 0 := Subsingleton.elim _ _
        simpa only [hi] using hn
  obtain ⟨n, rfl⟩ := he
  refine ⟨n, rfl, ?_⟩
  intro m hm
  have hh := congrArg depth hm
  simpa only [iterate_depth] using hh.symm

def p (t : GroundTerm exampleLanguage) : GroundAtom exampleLanguage :=
  ⟨1, Relations.p, fun _ => t⟩

def workedInstances : Finset (PropFormula (GroundAtom exampleLanguage)) :=
  { .atom (p c), .impl (.atom (p c)) (.atom (p (f c))),
    .impl (.atom (p (f c))) (.atom (p (f (f c)))), .neg (.atom (p (f (f c)))) }

theorem worked_instances_unsatisfiable : ¬ Satisfiable workedInstances := by
  classical
  rintro ⟨b, hb⟩
  have hc := hb (.atom (p c)) (by simp [workedInstances])
  have hc₁ := hb (.impl (.atom (p c)) (.atom (p (f c)))) (by simp [workedInstances])
  have hc₂ := hb (.impl (.atom (p (f c))) (.atom (p (f (f c))))) (by simp [workedInstances])
  have hn := hb (.neg (.atom (p (f (f c))))) (by simp [workedInstances])
  simp only [Satisfies, eval, Bool.or_eq_true, Bool.not_eq_true', Bool.eq_false_iff] at *
  tauto

def propagationBody : exampleLanguage.BoundedFormula Empty 1 :=
  (BoundedFormula.rel Relations.p (fun _ => .var (.inr 0))).imp
    (BoundedFormula.rel Relations.p
      (fun _ => .func Functions.f (fun _ => .var (.inr 0))))

def workedTheory : exampleLanguage.Theory :=
  {(p c).toFormula, propagationBody.all, (p (f (f c))).toFormula.not}

theorem worked_theory_unsatisfiable : ¬ workedTheory.IsSatisfiable := by
  classical
  rintro ⟨M⟩
  have hm : M ⊨ workedTheory := inferInstance
  have hc := hm.realize_of_mem (p c).toFormula (by simp [workedTheory])
  have hs := hm.realize_of_mem propagationBody.all (by simp [workedTheory])
  have hn := hm.realize_of_mem (p (f (f c))).toFormula.not (by simp [workedTheory])
  simp only [Sentence.Realize, Formula.Realize, Atom.toFormula, p, Relations.formula,
    Relations.boundedFormula, BoundedFormula.Realize, Term.realize_relabel,
    Function.comp_def, Term.realize, c, f, propagationBody] at hc hs hn
  exact hn (hs _ (hs _ hc))

/-- The same unary relation with no functions, not even constants. -/
def noConstantLanguage : Language := ⟨fun _ => Empty, Relations⟩

theorem no_ground_terms : IsEmpty (GroundTerm noConstantLanguage) := by
  refine ⟨?_⟩
  intro t
  cases t with
  | var x => exact x.elim
  | func f _ => exact f.elim

def contradictoryBody : noConstantLanguage.BoundedFormula Empty 1 :=
  let A := BoundedFormula.rel Relations.p (fun _ => .var (.inr 0))
  A ⊓ A.not

theorem contradictoryBody_relational : RelationalQF contradictoryBody := by
  change (True ∧ ((True ∧ True) ∧ True)) ∧ True
  trivial

noncomputable def contradictoryMatrix : Matrix noConstantLanguage :=
  ⟨1, contradictoryBody, contradictoryBody_relational⟩

theorem empty_ground_tests :
    Lemmatheca.MathematicalLogic.PropositionalCompactness.TheorySatisfiable
        (groundTheory {contradictoryMatrix}) ∧
      ¬ (universalTheory {contradictoryMatrix}).IsSatisfiable := by
  classical
  let _ := no_ground_terms
  constructor
  · refine ⟨fun _ => false, ?_⟩
    rintro P ⟨A, hA, ts, rfl⟩
    have he : A = contradictoryMatrix := Set.mem_singleton_iff.mp hA
    subst A
    change Fin 1 → GroundTerm noConstantLanguage at ts
    exact isEmptyElim (ts 0)
  · rintro ⟨M⟩
    have hm : M ⊨ universalTheory {contradictoryMatrix} := inferInstance
    have hh := hm.realize_of_mem contradictoryBody.all
      ⟨contradictoryMatrix, Set.mem_singleton _, rfl⟩
    simp [contradictoryBody, Sentence.Realize, Formula.Realize] at hh

abbrev twoConstants : Language := Language.constantsOn Bool
def firstConstant : GroundTerm twoConstants := Constants.term false
def secondConstant : GroundTerm twoConstants := Constants.term true

theorem equality_not_independent {M : Type*} [twoConstants.Structure M] :
    ¬ M ⊨ (firstConstant.equal firstConstant).not ∧
      ∃ v : Valuation Unit, Satisfies v (.neg (.atom ())) := by
  constructor
  · simp [Sentence.Realize, Formula.Realize, Term.equal, Term.bdEqual,
      BoundedFormula.Realize]
  · exact ⟨fun _ => false, rfl⟩

@[instance_reducible]
def unitConstants : twoConstants.Structure Unit :=
  Language.constantsOn.structure (fun _ : Bool => ())

theorem equality_needs_quotient :
    @Sentence.Realize twoConstants Unit unitConstants (firstConstant.equal secondConstant) ∧
      ¬ @Sentence.Realize twoConstants (GroundTerm twoConstants)
        (termStructure (fun _ => false)) (firstConstant.equal secondConstant) := by
  constructor
  · change (() : Unit) = ()
    rfl
  · simp only [Sentence.Realize, Formula.Realize, Term.equal, Term.bdEqual,
      BoundedFormula.Realize, Term.realize_relabel, Function.comp_def, Sum.elim_inl]
    have he : (default : Empty → GroundTerm twoConstants) = Empty.elim := Subsingleton.elim _ _
    simp only [he, ground_term_self]
    simp only [firstConstant, secondConstant, Constants.term]
    intro hh
    injection hh with h₀ hf
    exact Bool.false_ne_true hf

end
end Lemmatheca.Entry.HerbrandModels
